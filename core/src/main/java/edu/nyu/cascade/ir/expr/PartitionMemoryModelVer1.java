package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Map;
import java.util.Iterator;
import java.util.concurrent.ExecutionException;

import xtc.tree.GNode;
import xtc.type.DynamicReference;
import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.AliasAnalysis;
import edu.nyu.cascade.c.preprocessor.AliasVar;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;

/**
 * Monolithic memory mode, with a multiple memory arrays for multiple
 * variables. These arrays map a pointer to actual cell, where cell type 
 * is union of pointer type and scalar type. We also have a default
 * Merge Array, whenever an alias relation is detected among two arrays
 * by pointer assignment, just put both of them into the Merge Array.
 * However, currently, we have no clue how to merge arrays based on smtlib.
 *  
 * @author Wei
 *
 */

public class PartitionMemoryModelVer1 extends AbstractMonoMemoryModel {

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static PartitionMemoryModelVer1 create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new PartitionMemoryModelVer1(encoding);
  }

  private static final String ARRAY_MEM_PREFIX = "arr_of_m_";
  private static final String ARRAY_ALLOC_PREFIX = "arr_of_alloc_";
  
  private BitVectorType addrType, cellType;
  private RecordType memType, allocType; // with multiple array types
  private TupleType stateType;
  
  private final Map<String, Expression> lvals; // lvals: variables in stack
  private final List<Expression> stackRegions, heapRegions;
  private final Map<String, Expression> currentMemElems, currentAllocElems;
  
  private AliasAnalysis analyzer = null;
  private Expression prevDerefState = null;
  private ExpressionClosure currentState = null;
  
  private final LoadingCache<Pair<GNode, String>, AliasVar> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<Pair<GNode, String>, AliasVar>(){
        public AliasVar load(Pair<GNode, String> key) {
          return getRepVar(key.fst());
        }
      });
  
  private PartitionMemoryModelVer1(ExpressionEncoding encoding) {
    super(encoding);
    
    ExpressionManager exprManager = getExpressionManager();
    
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    this.cellType = exprManager.bitVectorType(size);
    this.addrType = exprManager.bitVectorType(size);
    
    List<String> elemNames = Lists.newArrayList();
    List<Type> elemTypes = Lists.newArrayList();
    this.memType = exprManager.recordType(
        Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), 
        elemNames, elemTypes);
    this.allocType = exprManager.recordType(
        Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), 
        elemNames, elemTypes);
    this.stateType = exprManager.tupleType(
        Identifiers.uniquify(DEFAULT_STATE_TYPE), memType, allocType);
    
    this.lvals = Maps.newHashMap();
    this.heapRegions = Lists.newArrayList();
    this.stackRegions = Lists.newArrayList();
    
    this.currentMemElems = Maps.newLinkedHashMap();
    this.currentAllocElems = Maps.newLinkedHashMap();
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( cellType ));

    ExpressionManager em = getExpressionManager();
    
    String regionName = Identifiers.uniquify(REGION_VARIABLE_NAME);
    Expression region = em.variable(regionName, addrType, false);
    GNode regionNode = GNode.create("PrimaryIdentifier", regionName);
    xtc.type.Type regionType = CType.unwrapped((xtc.type.Type) ptr.getNode().getProperty(TYPE));
    regionType = regionType.annotate().shape(new DynamicReference(regionName, regionType));
    regionType.mark(regionNode);
    String regionScope = ptr.getNode().getStringProperty(SCOPE);
    regionNode.setProperty(SCOPE, regionScope);
    region.setNode(regionNode);
    
    heapRegions.add(region); // For dynamic memory allocation, add to the end
    
    AliasVar ptr_var = loadRepVar(ptr.getNode());
    AliasVar region_var = analyzer.addVariable(regionName, regionScope, regionType);
    analyzer.addrAssign(ptr_var, region_var);
    
    /* Update memory and alloc state */
    initCurrentMemElems(state.getChild(0));
    
    { /* Add newly allocated region array to current memory elements */
      String regionArrName = getMemArrElemName(region_var);
      if(!currentMemElems.containsKey(regionArrName)) {
        Type cellType = getArrayElemType(region_var.getType());
        ArrayType arrType = em.arrayType(addrType, cellType);
        ArrayExpression regionArr = em.variable(regionArrName, arrType, false).asArray();
        currentMemElems.put(regionArrName, regionArr);
      }
    }
    
    { /* Update the pointer array in current memory elements */  
      String ptrRepArrName = getMemArrElemName(ptr_var);
      if(currentMemElems.containsKey(ptrRepArrName)) {
        ArrayExpression ptrRepArr = currentMemElems.get(ptrRepArrName).asArray();
//        Type cellType = ptrRepArr.getType().getElementType();
//        locVar = castExprToCell(locVar, cellType);
        ptrRepArr = ptrRepArr.update(ptr, region);
        currentMemElems.put(ptrRepArrName, ptrRepArr);
      } else {
        xtc.type.Type ptrRepVarType = ptr_var.getType();
        Type cellType = getArrayElemType(ptrRepVarType);
        ArrayType arrType = em.arrayType(addrType, cellType);
        ArrayExpression ptrRepArr = em.variable(ptrRepArrName, arrType, false).asArray();
        assert(cellType.equals(region.getType()));
        ptrRepArr = ptrRepArr.update(ptr, region);
        currentMemElems.put(ptrRepArrName, ptrRepArr);
      }
    }
    
    Type currentMemType = getCurrentMemoryType();    
    RecordExpression memory = em.record(currentMemType, currentMemElems.values());
    RecordExpression alloc = updateAllocState(state.getChild(1), region, size);
    TupleExpression statePrime = getUpdatedState(state, memory, alloc);
    
    memType = memory.getType();
    stateType = statePrime.getType();
    
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( cellType ));
    
    stackRegions.add(ptr);
    RecordExpression alloc = updateAllocState(state.getChild(1), ptr, size);
    return getUpdatedState(state, state.getChild(0), alloc);
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( cellType ));
    
    stackRegions.add(ptr);
    RecordExpression alloc = updateAllocState(state.getChild(1), ptr, size);
    return getUpdatedState(state, state.getChild(0), alloc);
  }
  
  @Override
  public TupleExpression free(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( addrType )); 
    Expression alloc = updateAllocState(state.getChild(1), ptr, 
        getExpressionManager().bitVectorZero(cellType.getSize()));
    
    return getUpdatedState(state, state.getChild(0), alloc);
  }

  @Override
  public TupleExpression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(lval.getType().equals( addrType ));
    RecordExpression memory = updateMemoryState(state.getChild(0), lval, rval);
    TupleExpression statePrime = getUpdatedState(state, memory, state.getChild(1));
    
    memType = memory.getType();
    stateType = statePrime.getType();
    
    return statePrime;
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    Preconditions.checkArgument(addrType.equals(p.getType()));
    
    // Initialization
    if(currentMemElems.isEmpty() || state != prevDerefState) {
      initCurrentMemElems(state.getChild(0));
      prevDerefState = state;
    }
    
    ExpressionManager em = getExpressionManager();
    
    Expression pValCell = null;
    AliasVar pRepVar = loadRepVar(p.getNode());
    
    String pArrName = getMemArrElemName(pRepVar);
    if(currentMemElems.containsKey(pArrName)) {
      ArrayExpression pArray = currentMemElems.get(pArrName).asArray();
      pValCell = pArray.index(p);
    } else { // Add an element to currentMemElem
      Type cellType = getArrayElemType(pRepVar.getType());
        
      ArrayType arrType = em.arrayType(addrType, cellType);
      ArrayExpression pArray = em.variable(pArrName, arrType, false).asArray();
      currentMemElems.put(pArrName, pArray);
      pValCell = pArray.index(p);
      
      Type currentMemType = getCurrentMemoryType();
      Expression memPrime = em.record(currentMemType, currentMemElems.values());
//      if(currentAlloc == null)    currentAlloc = state.getChild(1);
      //TODO: fix later for allocated
      Expression statePrime = getUpdatedState(state, memPrime, state.getChild(1));
      currentState = suspend(state, statePrime);    
    }
    return pValCell;
  }
  
  @Override
  public TupleExpression havoc(
      Expression state,
      Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( addrType ));
    Expression rval = getExpressionEncoding().getIntegerEncoding().unknown(); 
    RecordExpression memory = updateMemoryState(state.getChild(0), lval, rval); 
    TupleExpression statePrime = getUpdatedState(state, memory, state.getChild(1));
    
    memType = memory.getType();
    stateType = statePrime.getType();
        
    return statePrime;
  }
  
  @Override
  public Expression createLval(String name) {
    ExpressionManager exprManager = getExpressionManager();
    VariableExpression res = exprManager.variable(name, addrType, true);
    lvals.put(name, res);
    return res;
  }
  
  @Override
  public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( cellType ));
    
    ExpressionManager exprManager = getExpressionManager();

    AliasVar repVar = loadRepVar(ptr.getNode());
    analyzer.heapAssign(repVar, (xtc.type.Type) ptr.getNode().getProperty(TYPE));
    IOUtils.debug().pln(analyzer.displaySnapShort());
    
    Expression locVar = exprManager.variable(REGION_VARIABLE_NAME, addrType, true);
    
    heapRegions.add(locVar); // For dynamic memory allocation, add to the end
    
    Expression currentMem = updateMemoryState(state.getChild(0), ptr, locVar);
    Expression currentAlloc = updateAllocState(state.getChild(1), locVar, size);
    Expression statePrime = getUpdatedState(state, currentMem, currentAlloc);
    currentState = suspend(state, statePrime);
    
    return valid_malloc(state, locVar, size);
  }
  
  @Override
  public Expression addressOf(Expression content) {
    Preconditions.checkArgument(content.getNode().hasProperty(TYPE));
    xtc.type.Type type = (xtc.type.Type) content.getNode().getProperty(TYPE);
    while(type.isAlias() || type.isAnnotated() || type.isVariable()) {
      type = type.resolve();
      type = type.deannotate();
    }
    if(type.isArray() || type.isStruct() || type.isUnion())
      return content;
    else
      return content.getChild(1);
  }
  
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
    if (Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
      /* No comparable predicate defined in uninterpreted type */
      throw new UnsupportedOperationException(
          "--order-alloc is not supported in partition memory model");
    }
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    try {      
      //TODO: get the regions for each partition
      if (Preferences.isSet(Preferences.OPTION_SOUND_ALLOC)) {
        ExpressionManager exprManager = getExpressionManager();
        
        { /* The disjointness of stack variables, and != nullRef*/
          Expression nullRef = ((PointerExpressionEncoding) getExpressionEncoding())
              .getPointerEncoding().nullPtr().getChild(0);
          ImmutableList<Expression> distinctRef = new ImmutableList.Builder<Expression>()
              .addAll(lvals.values()).add(nullRef).build();
          if(distinctRef.size() > 1)  builder.add(exprManager.distinct(distinctRef));
        }
        
        { /* The disjointness between heap region and stack variable. */
          for(Expression heapRegion : heapRegions) {
            for(Expression lval : lvals.values()) {
              builder.add(lval.neq(heapRegion));
            }
          }
        }
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return builder.build();
  }

  @Override
  public Expression freshState() {
    ExpressionManager exprManager = getExpressionManager();
    Expression memVar = exprManager.variable(DEFAULT_MEMORY_VARIABLE_NAME, 
        memType, true);
    Expression allocVar = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, 
        allocType, true);
    return exprManager.tuple(stateType, memVar, allocVar);
  }
  
  @Override
  public RecordType getMemoryType() {
    return memType;
  }
  
  @Override
  public TupleType getStateType() {
    return stateType;
  }
  
  public void setStateType(TupleType stateType) {
    this.stateType = stateType;
    this.memType = stateType.asTuple().getElementTypes().get(0).asRecord();
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
//    Preconditions.checkArgument(stateType.equals(memoryVar.getType()));
    return new ExpressionClosure() {
      @Override
      public Expression eval(final Expression memory) {
//        Preconditions.checkArgument(memory.getType().equals(memoryVar.getType()));
        if(!isState(expr)) {
          // For non-tuple expression evaluation
          Expression exprPrime = expr;
          
          /* Substitute the memory of expr */
          Expression memVar_mem = memoryVar.getChild(0);
          Expression memory_mem = memory.getChild(0);
          
          Map<String, Expression> memVarMemMap = getMemElems(memVar_mem);
          Map<String, Expression> memoryMemMap = getMemElems(memory_mem);
          
          List<Expression> oldArgs_mem = Lists.newLinkedList();
          List<Expression> newArgs_mem = Lists.newLinkedList();
          
          for(String name : memVarMemMap.keySet()) {
            if(memoryMemMap.containsKey(name)) {
              oldArgs_mem.add(memVarMemMap.get(name));
              newArgs_mem.add(memoryMemMap.get(name));
            }
          }
          
          if(!oldArgs_mem.isEmpty()) {
            exprPrime = exprPrime.subst(oldArgs_mem, newArgs_mem);
            oldArgs_mem.clear(); newArgs_mem.clear();
          }
          
          /* Substitute the memory of expr */
          Expression memVar_alloc = memoryVar.getChild(1);
          Expression memory_alloc = memory.getChild(1);
          
          Map<String, Expression> memVarAllocMap = getMemElems(memVar_alloc);
          Map<String, Expression> memoryAllocMap = getMemElems(memory_alloc);
          
          List<Expression> oldArgs_alloc = Lists.newLinkedList();
          List<Expression> newArgs_alloc = Lists.newLinkedList();
          
          for(String name : memVarAllocMap.keySet()) {
            if(memoryAllocMap.containsKey(name)) {
              oldArgs_mem.add(memVarAllocMap.get(name));
              newArgs_mem.add(memoryAllocMap.get(name));
            }
          }
          
          if(!oldArgs_alloc.isEmpty()) {
            exprPrime = exprPrime.subst(oldArgs_alloc, newArgs_alloc);
            oldArgs_alloc.clear(); newArgs_alloc.clear();
          }
          
          return exprPrime.setNode(expr.getNode());
        } else {
          /* For tuple expression evaluation over memoryVar, since substitution doesn't return
           * right children for as tuple expression for state.
           */
          ExpressionManager exprManager = getExpressionManager();
          
          Expression memory_mem = memory.getChild(0);
          Expression memory_alloc = memory.getChild(1);
          Expression memPrime = null, allocPrime = null;
          
          {
            /* Substitute the memory of expr to memPrime */
            Expression expr_mem = expr.getChild(0);
            RecordType expr_mem_type = expr_mem.getType().asRecord();
            
            /* Initialize elemMap from the expr_mem */
            Map<String, Expression> elemMap = Maps.newLinkedHashMap();
            
            Iterator<String> nameItr = expr_mem_type.getElementNames().iterator();
            Iterator<? extends Expression> elemItr = expr_mem.getChildren().iterator();
            while(nameItr.hasNext() && elemItr.hasNext()) {
              String name = nameItr.next();
              Expression elem = elemItr.next();
              elem = elem.subst(memoryVar.getChild(0), memory_mem);
              elem = elem.subst(memoryVar.getChild(1), memory_alloc);
              elemMap.put(name, elem);
            }
            memPrime = exprManager.record(expr_mem_type, elemMap.values());
          }

          {
            /* Substitute the memory of expr to memPrime */
            Expression expr_alloc = expr.getChild(1);
            RecordType expr_alloc_type = expr_alloc.getType().asRecord();
          
            /* Initialize elemMap from the expr_mem */
            Map<String, Expression> elemMap = Maps.newLinkedHashMap();
          
            Iterator<String> nameItr = expr_alloc_type.getElementNames().iterator();
            Iterator<? extends Expression> elemItr = expr_alloc.getChildren().iterator();
            while(nameItr.hasNext() && elemItr.hasNext()) {
              String name = nameItr.next();
              Expression elem = elemItr.next();
              elem = elem.subst(memoryVar.getChild(0), memory_mem);
              elem = elem.subst(memoryVar.getChild(1), memory_alloc);
              elemMap.put(name, elem);
            }
          
            allocPrime = exprManager.record(expr_alloc_type, elemMap.values());
          }
          
          /* Update memType, allocType and stateType -- static member of memory model */
          memType = memPrime.getType().asRecord();
          allocType = allocPrime.getType().asRecord();
          stateType = expr.getType().asTuple();
          
          return exprManager.tuple(expr.getType(), memPrime, allocPrime);
        }
      }

      @Override
      public Type getOutputType() {
        return expr.getType();
      }

      @Override
      public Type getInputType() {
        return memoryVar.getType();
      }

      @Override
      public ExpressionManager getExpressionManager() {
        return expr.getExpressionManager();
      }
      
      private boolean isState(Expression expr) {
        return expr.getType().isTuple() 
            && expr.getType().asTuple().getName().startsWith(DEFAULT_STATE_TYPE);
      }
    };
  }
  
  @Override
  public ExpressionClosure getCurrentState() {
    return currentState;
  }
  
  @Override
  public void clearCurrentState() {
    currentMemElems.clear();
    currentAllocElems.clear();
    currentState = null;
  }
  
  public Expression combinePreMemoryStates(BooleanExpression guard, 
      RecordExpression mem_1, RecordExpression mem_0) {    
    
    RecordType memType_1 = mem_1.getType();
    Iterable<String> elemNames_1 = pickFieldNames(memType_1.getElementNames());
    
    RecordType memType_0 = mem_0.getType();
    final Iterable<String> elemNames_0 = pickFieldNames(memType_0.getElementNames());
    
    Iterable<String> commonElemNames = Iterables.filter(elemNames_1, 
        new Predicate<String>(){
      @Override
      public boolean apply(String elemName) {
        return Iterables.contains(elemNames_0, elemName);
      }
    });
    
    List<Expression> elems = Lists.newArrayListWithCapacity(
        Iterables.size(commonElemNames));
    List<Type> elemTypes = Lists.newArrayListWithCapacity(
        Iterables.size(commonElemNames));
    
    ExpressionManager em = getExpressionManager();
    final String arrName_1 = memType_1.getName();
    final String arrName_0 = memType_0.getName();
    
    Iterable<String> elemNames_1_prime = recomposeFieldNames(arrName_1, commonElemNames);
    Iterable<String> elemNames_0_prime = recomposeFieldNames(arrName_0, commonElemNames);
    Iterator<String> elemNames_1_prime_itr = elemNames_1_prime.iterator();
    Iterator<String> elemNames_0_prime_itr = elemNames_0_prime.iterator();
    
    while(elemNames_1_prime_itr.hasNext() && elemNames_0_prime_itr.hasNext()) {
      String elemName_1 = elemNames_1_prime_itr.next();
      String elemName_0 = elemNames_0_prime_itr.next();
      Expression elem = em.ifThenElse(guard, mem_1.select(elemName_1), mem_0.select(elemName_0));
      elems.add(elem);
      elemTypes.add(elem.getType());
    }
    
    final String arrName = Identifiers.uniquify(DEFAULT_MEMORY_VARIABLE_NAME);
    Iterable<String> elemNames = recomposeFieldNames(arrName, commonElemNames);
    
    RecordType recordType = em.recordType(Identifiers.uniquify(DEFAULT_MEMORY_VARIABLE_NAME), 
        elemNames, elemTypes);
    Expression res = em.record(recordType, elems);
    
    return res;
  }
  
  @Override
  protected RecordExpression updateMemoryState(Expression memState, Expression lval, Expression rval) {
    initCurrentMemElems(memState);
    
    ExpressionManager em = getExpressionManager();
    boolean memTypeChanged = false;

    AliasVar lvalRepVar = loadRepVar(lval.getNode());    
    String lvalRepArrName = getMemArrElemName(lvalRepVar);
    
    if(currentMemElems.containsKey(lvalRepArrName)) {
      ArrayExpression lvalRepArr = currentMemElems.get(lvalRepArrName).asArray();
//      Type cellType = lvalRepArr.getType().getElementType();
//      rval = castExprToCell(rval, cellType);
      lvalRepArr = lvalRepArr.update(lval, rval);
      currentMemElems.put(lvalRepArrName, lvalRepArr);
    } else {
      xtc.type.Type lvalRepType = lvalRepVar.getType();
      Type cellType = getArrayElemType(lvalRepType);
      ArrayType arrType = em.arrayType(addrType, cellType);
      ArrayExpression lvalArr = em.variable(lvalRepArrName, arrType, false).asArray();
//      rval = castExprToCell(rval, cellType);
      lvalArr = lvalArr.update(lval, rval);
      currentMemElems.put(lvalRepArrName, lvalArr);
      memTypeChanged = true;
    }
    
    Type currentMemType = memTypeChanged ? getCurrentMemoryType() : memState.getType();
    return em.record(currentMemType, currentMemElems.values());
  }
  
  protected RecordExpression updateAllocState(Expression allocState, Expression lval, Expression rval) {
    initCurrentAllocElems(allocState);
    
    ExpressionManager em = getExpressionManager();
    boolean allocTypeChanged = false;

    AliasVar lvalRepVar = loadRepVar(lval.getNode());
//    xtc.type.Type lvalRepType = lvalRepVar.getType();
    
    String lvalRepArrName = getAllocArrElemName(lvalRepVar);
    if(currentAllocElems.containsKey(lvalRepArrName)) {
      ArrayExpression lvalRepArr = currentAllocElems.get(lvalRepArrName).asArray();
//      Type cellType = lvalRepArr.getType().getElementType();
//      rval = castExprToCell(rval, cellType);
      lvalRepArr = lvalRepArr.update(lval, rval);
      currentAllocElems.put(lvalRepArrName, lvalRepArr);
    } else {
//      Type cellType = getArrayElemType(lvalRepType);
      ArrayType arrType = em.arrayType(addrType, cellType);
      ArrayExpression lvalArr = em.variable(lvalRepArrName, arrType, false).asArray();
//      rval = castExprToCell(rval, cellType);
      lvalArr = lvalArr.update(lval, rval);
      currentAllocElems.put(lvalRepArrName, lvalArr);
      allocTypeChanged = true;
    }
    
    Type currentAllocType = allocTypeChanged ? getCurrentAllocType() : allocState.getType();
    return em.record(currentAllocType, currentAllocElems.values());
  }
  
  @Override
  public Expression castExpression(Expression state, Expression src, xtc.type.Type type) {
    if(type.isPointer() && src.isBitVector()) {
      return ((PointerExpressionEncoding) getExpressionEncoding())
          .getPointerEncoding().nullPtr();
    }
    return src;
  }
  
  @Override
  public void setAliasAnalyzer(AliasAnalysis analyzer) {
    this.analyzer = analyzer;
    IOUtils.debug().pln(analyzer.displaySnapShort());
  }
  
  /**
   * Recreate state from @param memoryPrime and @param allocPrime and create a new state
   * type if state type is changed from the type of state
   * @return a new state
   */
  public TupleExpression getUpdatedState(Expression state, Expression memoryPrime, Expression allocPrime) {
    ExpressionManager em = getExpressionManager();
    Type stateTypePrime = null;
    
    if(state != null 
        && state.getType().asTuple().getElementTypes().get(0).equals(memoryPrime.getType())
        && state.getType().asTuple().getElementTypes().get(1).equals(allocPrime.getType())) {
      stateTypePrime = state.getType();
    } else {
      stateTypePrime = em.tupleType(Identifiers.uniquify(DEFAULT_STATE_TYPE), 
          memoryPrime.getType(), allocPrime.getType());
    }
    
    return em.tuple(stateTypePrime, memoryPrime, allocPrime);
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    
    List<BooleanExpression> disjs = Lists.newArrayList();
    
//    try {
//      ExpressionManager exprManager = getExpressionManager();
//      
//      assert ptr.getNode().hasName("AddressOf");
//      GNode gnode = ptr.getNode().getGeneric(0);
//      xtc.type.Type type = (xtc.type.Type) gnode.getProperty(TYPE);
//      String scope = gnode.getStringProperty(SCOPE);
//      String refName = CType.getReferenceName(type);
//      
//      AliasVar repVar = analyzer.getRepVar(refName, scope, type);
//      
//      Expression alloc = state.getChild(1);
//      String pArrName = getMemArrElemName(repVar);
//      if(currentMemElems.containsKey(pArrName)) {
//      
//      Expression ref_ptr = ptr.asTuple().index(0);
//      Expression off_ptr = ptr.asTuple().index(1);
//      Expression sizeZro = exprManager.bitVectorZero(offType.getSize());
//      Expression nullRef = ((PointerExpressionEncoding) getExpressionEncoding())
//          .getPointerEncoding().nullPtr().asTuple().getChild(0);
//      
//      // Valid stack access
//      for( Expression lval : lvals.values()) {
//        Expression sizeVar = alloc.asArray().index(lval);
//        disjs.add(
//            exprManager.and(
//                ref_ptr.eq(lval), 
//                /* aggregate variable: size > 0; scalar variable: size = 0 */
//                exprManager.ifThenElse( 
//                    exprManager.greaterThan(sizeVar, sizeZro),
//                    exprManager.and(
//                        exprManager.greaterThanOrEqual(off_ptr, sizeZro),
//                        exprManager.lessThan(off_ptr, sizeVar)),
//                    off_ptr.eq(sizeVar))));
//      }
//      
//      // Valid heap access
//      for( Expression refVar : heapRegions ) {
//        /* ptr:(ref_ptr, off), startPos:(ref, 0), endPos:(ref, size);
//         * ensure ref_ptr == ref && 0 <= off && off < size
//         */
//        Expression sizeVar = alloc.asArray().index(refVar);
//        disjs.add(
//            exprManager.and(
//                refVar.neq(nullRef),
//                ref_ptr.eq(refVar),
//                exprManager.lessThanOrEqual(sizeZro, off_ptr),
//                exprManager.lessThan(off_ptr, sizeVar)));
//      }
//    } catch (TheoremProverException e) {
//      throw new ExpressionFactoryException(e);
//    }
    return getExpressionManager().or(disjs);
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( cellType ));
    
    List<BooleanExpression> disjs = Lists.newArrayList();
    
//    try {
//      ExpressionManager exprManager = getExpressionManager();
//      Expression alloc = state.getChild(1);
//      Expression ref_ptr = ptr.asTuple().index(0);
//      Expression off_ptr = ptr.asTuple().index(1);
//      Expression off_bound = exprManager.plus(offType.getSize(), off_ptr, size);
//      Expression sizeZro = exprManager.bitVectorZero(offType.getSize());
//      Expression nullRef = ((PointerExpressionEncoding) getExpressionEncoding())
//          .getPointerEncoding().nullPtr().asTuple().getChild(0);
//      
//      // Valid stack access
//      for( Expression lval : lvals.values()) {
//        Expression sizeVar = alloc.asArray().index(lval);
//        disjs.add(
//            exprManager.and(
//                ref_ptr.eq(lval), 
//                /* aggregate variable: size > 0; scalar variable: size = 0 */
//                exprManager.ifThenElse( 
//                    exprManager.greaterThan(sizeVar, sizeZro),
//                    exprManager.and(        
//                        exprManager.greaterThanOrEqual(off_ptr, sizeZro),
//                        exprManager.lessThan(off_bound, sizeVar)),
//                    off_ptr.eq(sizeVar)))); 
//      }
//      
//      // Valid heap access
//      for( Expression refVar : heapRegions ) {
//        Expression sizeVar = alloc.asArray().index(refVar);
//        /* ptr:(ref_ptr, off), startPos:(ref, 0), endPos:(ref, size);
//         * ensure ref_ptr == ref && 0 <= off && off < size
//         */
//        disjs.add(
//            exprManager.and(
//                refVar.neq(nullRef),
//                ref_ptr.eq(refVar), 
//                exprManager.lessThanOrEqual(sizeZro, off_ptr),
//                exprManager.lessThan(off_bound, sizeVar)));
//      }
//    } catch (TheoremProverException e) {
//      throw new ExpressionFactoryException(e);
//    }
    return getExpressionManager().or(disjs);
  }
  
  @Override
  public BooleanExpression valid_malloc(Expression state, Expression ptr, Expression size) {
    ExpressionManager exprManager = getExpressionManager();
    
    if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
      throw new UnsupportedOperationException(
          "--order-alloc is not supported in partition memory model");
    } 
    
    if (Preferences.isSet(Preferences.OPTION_SOUND_ALLOC)) {
      Expression alloc = state.getChild(1);
      
      ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
      
      Expression nullPtr = ((PointerExpressionEncoding) getExpressionEncoding())
          .getPointerEncoding().nullPtr();
      Expression nullRef = nullPtr.asTuple().getChild(0);
      Expression sizeZro = exprManager.bitVectorZero(cellType.getSize());
      
      Expression assump = exprManager.neq(ptr, nullPtr);
      
      builder.add(exprManager.neq(ptr, nullPtr)); // ptr != null
      
      /* Only analyze heap part */
      
      List<Expression> regions = Lists.newArrayList(heapRegions);
      
      /* Collect all heap regions except the last one, the one just allocated. */
      regions.remove(regions.size()-1);
      
      for(Expression region : regions) {
        Expression region_size = alloc.asArray().index(region);
        
        Expression assump_local = exprManager.and(
            exprManager.greaterThan(region_size, sizeZro),
            exprManager.neq(region, nullRef)); // nullRef may also have non-zero size
        
        Expression assert_local = exprManager.neq(region, ptr.asTuple().index(0));
        
        builder.add(exprManager.implies(assump_local, assert_local));
      }
      
      return exprManager.implies(assump, exprManager.and(builder.build()));
    }
    
    return exprManager.tt();
  }
  
  @Override
  public BooleanExpression valid_free(Expression state, Expression ptr) {
//    ExpressionManager exprManager = getExpressionManager();
//    Expression alloc = state.getChild(1);
//    Expression nullPtr = exprManager.bitVectorZero(addrType.getSize())
//    return exprManager.or(exprManager.eq(ptr, nullPtr), exprManager.greaterThan(size, 
//        exprManager.bitVectorZero(cellType.getSize())));
    return getExpressionManager().tt();
  }
  
  @Override
  public Expression substAlloc(Expression expr) {
//    ExpressionManager exprManager = getExpressionManager();
//    Expression initialAlloc = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, allocType, false);
//    Expression constAlloc = exprManager.storeAll(exprManager.bitVectorZero(.getSize()), allocType);
//    Expression res = expr.subst(initialAlloc, constAlloc);
//    return res;
    return getExpressionManager().tt();
  }
    
  /**
   * Get representative alias variable in the pointer analyzer
   * @param gnode
   */
  private AliasVar getRepVar(GNode gnode) {
    Preconditions.checkArgument(gnode.hasProperty(TYPE) && gnode.hasProperty(SCOPE));
    
    xtc.type.Type type = (xtc.type.Type) gnode.getProperty(TYPE);
    String scope = gnode.getStringProperty(SCOPE);
    String refName = CType.getReferenceName(type);
    
    AliasVar repVar = analyzer.getRepVar(refName, scope, type);
    if(repVar.isNullLoc()) {
      throw new NullPointerException("null pointer reference of " + type.getShape());
    }
    return repVar;
  }
  
  /**
   * Load representative alias variable from cache
   * @param gnode
   */
  private AliasVar loadRepVar(GNode gnode) {
    try {
      String scope = gnode.getStringProperty(SCOPE);
      Pair<GNode, String> key = Pair.of(gnode, scope);
      return cache.get(key);
    } catch (ExecutionException e) {
      throw new ExpressionFactoryException(e);
    }
  }
  
/*  private ElemType getElemType(xtc.type.Type type) {
    Preconditions.checkArgument(CellKind.STRUCTORUNION.equals(CType.getCellKind(type)));
    StructOrUnionT su = CType.unwrapped(type).toStructOrUnion();
    boolean scalar = true, pointer = true;
    for(VariableT v : su.getMembers()) {
      switch(CType.getCellKind(v)) {
      case SCALAR :         pointer = false; break;
      case POINTER:         scalar = false; break;
      // FIXME: struct { int a[100] }, get the mix types?
      case ARRAY:
      case STRUCTORUNION:   scalar = false; pointer = false; break;
      default:              throw new IllegalArgumentException("Unsupported type " + v);
      }
    }
    assert(!(pointer && scalar));
    if(pointer)         return  ElemType.POINTER;
    else if(scalar)     return  ElemType.SCALAR;
    else                return  ElemType.MIX;
  }*/
  
/*  private Expression castExprToCell(Expression rval, Type cellType) {
    if(rval.getType().equals(cellType)) return rval;
    
    ExpressionManager exprManager = getExpressionManager();
    
    if(scalarType.equals(rval.getType())) {
      if(ptrType.equals(cellType)) {
        xtc.type.Type type = (xtc.type.Type) rval.getNode().getProperty(TYPE);
        assert type.hasConstant() ;
        if(type.getConstant().bigIntValue().intValue() == 0) {
          rval = ((PointerExpressionEncoding) getExpressionEncoding())
              .getPointerEncoding().nullPtr();
        } else {
          rval = getExpressionEncoding().unknown();
        }
      } else if(mixType.equals(cellType)) {
        rval = exprManager.construct(scalarConstr, rval);
      } else {
        throw new IllegalArgumentException("Invalid type " + rval.getType() + " to " + cellType);
      }
    } else if(ptrType.equals(rval.getType())) {
      if(mixType.equals(cellType)) {
        rval = exprManager.construct(ptrConstr, rval);
      } else {
        throw new IllegalArgumentException("Invalid type " + rval.getType() + " to " + cellType);
      }
    } else {
      throw new IllegalArgumentException("Invalid type " + rval.getType() + " to " + cellType);
    }
    return rval;
  }*/
  
  private String getMemArrElemName(AliasVar var) {
    StringBuilder sb = new StringBuilder();
    sb.append(ARRAY_MEM_PREFIX).append(var.getName()).append('_').append(var.getScope());
    return Identifiers.toValidId(sb.toString());
  }
  
  private String getAllocArrElemName(AliasVar var) {
    StringBuilder sb = new StringBuilder();
    sb.append(ARRAY_ALLOC_PREFIX).append(var.getName()).append('_').append(var.getScope());
    return Identifiers.toValidId(sb.toString());
  }
  
  /**
   * Get the cell tyoe of the array in memory record for node with certain type
   * @param type
   */
  private Type getArrayElemType(xtc.type.Type type) {
    Type resType = null;
    switch(CType.getCellKind(type)) {
    case SCALAR :
    case BOOL :     resType = cellType; break;
    case ARRAY : 
    case POINTER :  
    case STRUCTORUNION : resType = addrType; break;
    default:    throw new IllegalArgumentException("Unsupported type " + type);
    }
    return resType;
  }
  
  private RecordType getCurrentMemoryType() {
    return getCurrentRecordType(true);
  }
  
  private RecordType getCurrentAllocType() {
    return getCurrentRecordType(false);
  }
  
  private RecordType getCurrentRecordType(boolean mem) {
    ExpressionManager em = getExpressionManager();
    Map<String, Expression> currentElems = mem ? currentMemElems : currentAllocElems;
    final String arrName = mem ?  Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE) :
        Identifiers.uniquify(DEFAULT_ALLOC_STATE_TYPE);
    
    Iterable<Type> elemTypes = Iterables.transform(currentElems.values(), 
        new Function<Expression, Type>(){
      @Override
      public Type apply(Expression expr) {
        return expr.getType();
      }
    });
    
    if(elemTypes == null)
      throw new ExpressionFactoryException("Update failed.");
    
    Iterable<String> elemNames = recomposeFieldNames(arrName, currentElems.keySet());
    
    return em.recordType(arrName, elemNames, elemTypes);
  }
  
  private void initCurrentMemElems(Expression memState) {
    currentMemElems.putAll(getMemElems(memState));
  }
  
  private void initCurrentAllocElems(Expression allocState) {
    currentAllocElems.putAll(getMemElems(allocState));
  }
  
  private Map<String, Expression> getMemElems(Expression memState) {
    Preconditions.checkArgument(memState.isRecord());
    Map<String, Expression> resMap = Maps.newLinkedHashMap();
    RecordExpression mem = memState.asRecord();
    Iterable<String> elemNames = mem.getType().getElementNames();
    Iterable<String> fieldNames = pickFieldNames(elemNames);
    assert(Iterables.size(elemNames) == Iterables.size(fieldNames));
    Iterator<String> elemNameItr = elemNames.iterator();
    Iterator<String> fieldNameItr = fieldNames.iterator();
    while(elemNameItr.hasNext() && fieldNameItr.hasNext()) {
      String elemName = elemNameItr.next();
      String fieldName = fieldNameItr.next();
      Expression value = mem.select(elemName);
      resMap.put(fieldName, value);
    }
    return resMap;
  }
}
