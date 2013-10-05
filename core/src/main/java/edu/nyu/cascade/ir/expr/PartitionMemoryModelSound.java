package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Map;
import java.util.Iterator;
import java.util.Set;
import java.util.concurrent.ExecutionException;

import xtc.tree.GNode;
import xtc.tree.Node;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.AliasAnalysis;
import edu.nyu.cascade.c.preprocessor.AliasVar;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
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

/**
 * Partition memory mode, with a multiple memory arrays for multiple
 * variables. These arrays map a pointer to actual cell, where cell type 
 * is union of pointer type and scalar type. We also have a default
 * Merge Array, whenever an alias relation is detected among two arrays
 * by pointer assignment, just put both of them into the Merge Array.
 * However, currently, we have no clue how to merge arrays based on smtlib.
 *  
 * @author Wei
 *
 */

public class PartitionMemoryModelSound extends AbstractMonoMemoryModel {

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static PartitionMemoryModelSound create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new PartitionMemoryModelSound(encoding);
  }

  private static final String ARRAY_MEM_PREFIX = "arr_of_mem_";
  private static final String ARRAY_ALLOC_PREFIX = "arr_of_size_";
  
  private BitVectorType addrType, cellType;
  private RecordType memType, allocType; // with multiple array types
  private TupleType stateType;
  
  // Keep track of stack variables and allocated heap regions
  private final Map<Pair<String, String>, Expression> lvals, heapRegions;
  private final Set<Expression> stackRegions; // track the stack region variable
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
  
  private PartitionMemoryModelSound(ExpressionEncoding encoding) {
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
        Identifiers.uniquify(DEFAULT_ALLOC_STATE_TYPE), 
        elemNames, elemTypes);
    this.stateType = exprManager.tupleType(
        Identifiers.uniquify(DEFAULT_STATE_TYPE), memType, allocType);
    
    this.lvals = Maps.newLinkedHashMap();
    this.heapRegions = Maps.newLinkedHashMap();
    this.stackRegions = Sets.newHashSet();
    
    this.currentMemElems = Maps.newLinkedHashMap();
    this.currentAllocElems = Maps.newLinkedHashMap();
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( cellType ));

    ExpressionManager em = getExpressionManager();
    
    AliasVar ptr_var = loadRepVar(ptr.getNode());
    AliasVar region_var = analyzer.getAllocRegion(ptr_var);
    
    String regionName = region_var.getName();
    Expression region = em.variable(regionName, addrType, false);
    GNode regionNode = GNode.create("PrimaryIdentifier", regionName);
    xtc.type.Type regionType = region_var.getType();
    regionType.mark(regionNode);
    String regionScope = region_var.getScope();
    regionNode.setProperty(SCOPE, regionScope);
    region.setNode(regionNode);
    
    // For dynamic memory allocation, add to the end
    heapRegions.put(Pair.of(regionName, regionScope), region);
    
    { /* Add newly allocated region array to current memory elements */
      Iterable<String> elemNames = state.getChild(0).asRecord().getType().getElementNames();
      Iterable<String> fieldNames = pickFieldNames(elemNames);
      String regionArrName = getMemArrElemName(region_var);
      if(!Iterables.contains(fieldNames, regionArrName)) {
        Type cellType = getArrayElemType(region_var.getType());
        ArrayType arrType = em.arrayType(addrType, cellType);
        ArrayExpression regionArr = em.variable(regionArrName, arrType, false).asArray();
        currentMemElems.put(regionArrName, regionArr);
      }
    }
      
    RecordExpression memory = updateMemoryState(state.getChild(0), ptr, region);
    RecordExpression alloc = updateAllocState(state.getChild(1), region, size);
    TupleExpression statePrime = getUpdatedState(state, memory, alloc);
    setStateType(statePrime.getType());
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( cellType ));
    
    stackRegions.add(ptr);
    RecordExpression alloc = updateAllocState(state.getChild(1), ptr, size);
    TupleExpression statePrime = getUpdatedState(state, state.getChild(0), alloc);
    setStateType(statePrime.getType());
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( cellType ));
    
    stackRegions.add(ptr);
    RecordExpression alloc = updateAllocState(state.getChild(1), ptr, size);
    TupleExpression statePrime = getUpdatedState(state, state.getChild(0), alloc);
    setStateType(statePrime.getType());
    return statePrime;
  }
  
  @Override
  public TupleExpression free(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( addrType )); 
    Expression alloc = updateAllocState(state.getChild(1), ptr, 
        getExpressionManager().bitVectorZero(cellType.getSize()));
    
    TupleExpression statePrime = getUpdatedState(state, state.getChild(0), alloc);
    setStateType(statePrime.getType());
    return statePrime;
  }

  @Override
  public TupleExpression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(lval.getType().equals( addrType ));
    RecordExpression memory = updateMemoryState(state.getChild(0), lval, rval);
    TupleExpression statePrime = getUpdatedState(state, memory, state.getChild(1));
    setStateType(statePrime.getType());
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
      Expression allocPrime = updateAllocState(state.getChild(1));
      Expression statePrime = getUpdatedState(state, memPrime, allocPrime);
      setCurrentState(state, statePrime);    
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
    setStateType(statePrime.getType());
    return statePrime;
  }
  
  @Override
  public Expression createLval(String prefix, Node node) {
    Preconditions.checkArgument(node.hasProperty(SCOPE));
    Preconditions.checkArgument(node.hasName("PrimaryIdentifier") 
        || node.hasName("SimpleDeclarator"));
    ExpressionManager exprManager = getExpressionManager();
    String name = node.getString(0);
    String scope = node.getStringProperty(SCOPE);
    VariableExpression res = exprManager.variable(prefix+name, addrType, true);
    lvals.put(Pair.of(name, scope), res);
    return res;
  }
  
  @Override
  public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( cellType ));
    
    ExpressionManager exprManager = getExpressionManager();

    AliasVar ptr_var = loadRepVar(ptr.getNode());
    analyzer.heapAssign(ptr_var, (xtc.type.Type) ptr.getNode().getProperty(TYPE));
    AliasVar region_var = analyzer.getAllocRegion(ptr_var);
    
    String regionName = region_var.getName();
    Expression region = exprManager.variable(regionName, addrType, false);
    GNode regionNode = GNode.create("PrimaryIdentifier", regionName);
    xtc.type.Type regionType = region_var.getType();
    regionType.mark(regionNode);
    String regionScope = region_var.getScope();
    regionNode.setProperty(SCOPE, regionScope);
    region.setNode(regionNode);
    
    heapRegions.put(Pair.of(regionName, regionScope), region); // For dynamic memory allocation, add to the end
    
    Expression currentMem = updateMemoryState(state.getChild(0), ptr, region);
    Expression currentAlloc = updateAllocState(state.getChild(1), region, size);
    Expression statePrime = getUpdatedState(state, currentMem, currentAlloc);
    setCurrentState(state, statePrime);
    
    return valid_malloc(state, region, size, true);
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
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    try {
      initCurrentMemElems(state.getChild(0));
      initCurrentAllocElems(state.getChild(1));
      
      ExpressionManager exprManager = getExpressionManager();
      Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
      Expression sizeZro = exprManager.bitVectorZero(cellType.getSize());
      
      ImmutableMap<AliasVar, Set<AliasVar>> map = analyzer.snapshot();
      for(AliasVar repVar : map.keySet()) {
        String repVarMemArrName = getMemArrElemName(repVar);
        
        /* If the repVar is referred in the execution paths */
        if(!currentMemElems.containsKey(repVarMemArrName)) continue;
        
        /* Categorize vars into stVar, stReg, and hpReg */
        Iterable<AliasVar> equivAliasVars = analyzer.getEquivClass(repVar);
        Iterable<ImmutableList<Expression>> varSets = getCategorizedVars(equivAliasVars);
        
        /* The soundness of stack: distinctness of nullPtr and all stack variables 
         */
        Iterable<Expression> stVars = Iterables.get(varSets, 0);
        if (!Iterables.isEmpty(stVars))  {
          ImmutableList<Expression> distinctPtr = new ImmutableList.Builder<Expression>()
              .addAll(stVars).add(nullPtr).build();
          builder.add(exprManager.distinct(distinctPtr));
        }
        
        String allocArrName = getAllocArrElemName(repVar);
        
        if(currentAllocElems.containsKey(allocArrName)) {            
          ArrayExpression allocArr = currentAllocElems.get(allocArrName).asArray();
          
          /* The soundness of stack regions */
          Iterable<Expression> stRegs = Iterables.get(varSets, 1);
          for (Expression region : stRegs) {
            Expression regionSize = allocArr.index(region);
            BitVectorExpression regionBound = exprManager.plus(addrType
                .getSize(), region, regionSize);
            
            /* The upper bound of the stack region won't overflow */
            builder.add(exprManager.greaterThan(regionBound, region));
            
            /* Every stack variable doesn't falls into any stack region*/
            for(Expression lval : stVars) {
              builder.add(
                  exprManager.or(
                      exprManager.lessThan(lval, region),
                        exprManager.lessThanOrEqual(regionBound, lval)));
            }
            
            /* Every other stack region is non-overlapping. 
             * TODO: Could optimize using commutativity
             */
            for (Expression region2 : stRegs) {
              if (!region.equals(region2)) {
                BitVectorExpression regionBound2 = exprManager.plus(addrType
                    .getSize(), region2, allocArr.index(region2));
                
                builder.add(
                    exprManager.or(
                        exprManager.lessThanOrEqual(regionBound2, region),
                        exprManager.lessThanOrEqual(regionBound, region2)));
              }
            }
          } 
          
          /* Disjoint of the heap region or stack region/variable */
          Iterable<Expression> hpRegs = Iterables.get(varSets, 2);
          for (Expression region : hpRegs) {
            Expression regionSize = allocArr.index(region);
            BitVectorExpression regionBound = exprManager.plus(addrType.getSize(), region, regionSize);
            
            /* Disjoint of the heap region or stack variable */
            for (Expression lval : stVars) {
              builder.add(exprManager.implies(
                  // heap region is non-null and not freed before
                  exprManager.and(region.neq(nullPtr), regionSize.neq(sizeZro)),
                  exprManager.or(
                      exprManager.lessThan(lval, region),
                      exprManager.lessThanOrEqual(regionBound, lval))));
            }
            
            /* Disjoint of the heap region or stack region */
            for (Expression region2 : stRegs) {
              BitVectorExpression regionBound2 = exprManager.plus(addrType
                  .getSize(), region2, allocArr.index(region2));
              
              builder.add(exprManager.implies(
                  // heap region is non-null and not freed before
                  exprManager.and(region.neq(nullPtr), regionSize.neq(sizeZro)),
                  exprManager.or(
                      exprManager.lessThan(regionBound2, region),
                      exprManager.lessThanOrEqual(regionBound, region2))));
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
  public RecordType getAllocType() {
    return allocType;
  }
  
  @Override
  public TupleType getStateType() {
    return stateType;
  }
  
  public void setStateType(TupleType stateType) {
    this.stateType = stateType;
    this.memType = stateType.asTuple().getElementTypes().get(0).asRecord();
    this.allocType = stateType.asTuple().getElementTypes().get(1).asRecord();
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
          
          Map<String, Expression> memVarMemMap = getRecordElems(memVar_mem.asRecord());
          Map<String, Expression> memoryMemMap = getRecordElems(memory_mem.asRecord());
          
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
          
          /* Substitute the alloc of expr */
          Expression memVar_alloc = memoryVar.getChild(1);
          Expression memory_alloc = memory.getChild(1);
          
          Map<String, Expression> memVarAllocMap = getRecordElems(memVar_alloc.asRecord());
          Map<String, Expression> memoryAllocMap = getRecordElems(memory_alloc.asRecord());
          
          List<Expression> oldArgs_alloc = Lists.newLinkedList();
          List<Expression> newArgs_alloc = Lists.newLinkedList();
          
          for(String name : memVarAllocMap.keySet()) {
            if(memoryAllocMap.containsKey(name)) {
              oldArgs_alloc.add(memVarAllocMap.get(name));
              newArgs_alloc.add(memoryAllocMap.get(name));
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
          Expression expr_mem = expr.getChild(0);
          Expression expr_alloc = expr.getChild(1);
          Expression memPrime = memory_mem, allocPrime = memory_alloc;
          
          if(!memory_mem.getType().equals(expr_mem.getType())){
            /* Substitute the memory of expr to memPrime */
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
            memType = memPrime.getType().asRecord();
          }

          if(!memory_alloc.getType().equals(expr_alloc.getType())){
            /* Substitute the alloc of expr to memPrime */
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
          
          /* Update stateType -- static member of memory model */
          setStateType(expr.getType().asTuple());
          
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
    
    try {
      ExpressionManager exprManager = getExpressionManager();
                  
      /* Find related heap regions and alloc array */
      AliasVar pRepVar = loadRepVar(ptr.getNode());
      AliasVar ptr2RepVar = analyzer.getPointsToRepVar(pRepVar);
      Iterable<AliasVar> equivAliasVars = analyzer.getEquivClass(ptr2RepVar);
      
      Iterable<ImmutableList<Expression>> varSets = getCategorizedVars(equivAliasVars);
      
      /* Get the related alloc array */
      initCurrentAllocElems(state.getChild(1));
      String allocArrName = getAllocArrElemName(ptr2RepVar);
      assert currentAllocElems.containsKey(allocArrName);
      ArrayExpression allocArr = currentAllocElems.get(allocArrName).asArray();
      
      /* TODO: Check the scope of local variable, this will be unsound to take 
       * address of local variable out of scope */
      Iterable<Expression> stVars = Iterables.get(varSets, 0);
      for( Expression stVar : stVars)    disjs.add(ptr.eq(stVar));
      
      // In any stack region
      Iterable<Expression> stRegs = Iterables.get(varSets, 1);
      for(Expression region : stRegs) {
        Expression regionSize = allocArr.index(region);
        
        BitVectorExpression regionBound = exprManager.plus(addrType
            .getSize(), region, regionSize);
        disjs.add(
            exprManager.and(
                exprManager.lessThanOrEqual(region, ptr),
                exprManager.lessThan(ptr, regionBound)));
      }
      
      // In any heap region
      Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
      Expression sizeZro = exprManager.bitVectorZero(cellType.getSize());
      
      Iterable<Expression> hpRegs = Iterables.get(varSets, 2);
      for( Expression region : hpRegs ) {
        Expression regionSize = allocArr.index(region);        
        BitVectorExpression regionBound = exprManager.plus(addrType.getSize(), 
            region, regionSize);
        disjs.add(
            exprManager.and(
                region.neq(nullPtr),
                regionSize.neq(sizeZro),
                exprManager.lessThanOrEqual(region, ptr),
                exprManager.lessThan(ptr, regionBound)));
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return getExpressionManager().or(disjs);
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( cellType ));
    
    List<BooleanExpression> disjs = Lists.newArrayList();
    
    try {
      ExpressionManager exprManager = getExpressionManager();
      
      /* Find related heap regions and alloc array */
      AliasVar pRepVar = loadRepVar(ptr.getNode());
      AliasVar ptr2RepVar = analyzer.getPointsToRepVar(pRepVar);
      Iterable<AliasVar> equivAliasVars = analyzer.getEquivClass(ptr2RepVar);
      Iterable<ImmutableList<Expression>> varSets = getCategorizedVars(equivAliasVars);

      Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
      Expression sizeZro = exprManager.bitVectorZero(cellType.getSize());
      
      /* Get the related alloc array */
      initCurrentAllocElems(state.getChild(1));
      String allocArrName = getAllocArrElemName(ptr2RepVar);
      assert currentAllocElems.containsKey(allocArrName);
      ArrayExpression allocArr = currentAllocElems.get(allocArrName).asArray();
      
      /* TODO: Check the scope of local variable, this will be unsound to take 
       * address of local variable out of scope */ 
      Iterable<Expression> stVars = Iterables.get(varSets, 0);
      for( Expression stVar : stVars)    
        disjs.add(exprManager.and(ptr.eq(stVar), size.eq(sizeZro)));
      
      // In any stack region
      Iterable<Expression> stRegs = Iterables.get(varSets, 1);
      for(Expression region : stRegs) {
        Expression regionSize = allocArr.index(region);
        BitVectorExpression ptrBound = exprManager.plus(addrType.getSize(), 
            ptr, size);
        BitVectorExpression regionBound = exprManager.plus(addrType.getSize(), 
            region, regionSize);
        
        disjs.add(
            exprManager.and(
                exprManager.lessThanOrEqual(region, ptr),
                exprManager.lessThan(ptrBound, regionBound)));
      }
      
      // In any heap region
      Iterable<Expression> hpRegs = Iterables.get(varSets, 2);
      for( Expression region : hpRegs ) {
        Expression regionSize = allocArr.index(region);
        BitVectorExpression ptrBound = exprManager.plus(addrType.getSize(),
            ptr, size);
        BitVectorExpression regionBound = exprManager.plus(addrType.getSize(),
            region, regionSize);
        
        disjs.add(
            exprManager.and(
                region.neq(nullPtr), 
                regionSize.neq(sizeZro),
                exprManager.lessThanOrEqual(region, ptr),
                exprManager.lessThan(ptrBound, regionBound)));
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return getExpressionManager().or(disjs);
  }
  
  @Override
  public BooleanExpression valid_malloc(Expression state, Expression ptr, Expression size) {
    return valid_malloc(state, ptr, size, false);
  }
  
  @Override
  public BooleanExpression valid_free(Expression state, Expression ptr) {
    /* Find related heap regions and alloc array */
    AliasVar pRepVar = loadRepVar(ptr.getNode());
    AliasVar ptr2RepVar = analyzer.getPointsToRepVar(pRepVar);
    
    initCurrentAllocElems(state.getChild(1));
    String allocArrName = getAllocArrElemName(ptr2RepVar);
    assert currentAllocElems.containsKey(allocArrName);
    ArrayExpression allocArr = currentAllocElems.get(allocArrName).asArray();
    
    ExpressionManager exprManager = getExpressionManager();
    Expression size = allocArr.index(ptr);
    Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
    Expression sizeZro = exprManager.bitVectorZero(cellType.getSize());
    return exprManager.or(ptr.eq(nullPtr), exprManager.greaterThan(size, sizeZro));
  }
  
  @Override
  public Expression substAlloc(Expression expr) {
    return expr;
  }
  
  @Override
  protected RecordExpression updateMemoryState(Expression memState, Expression lval, Expression rval) {
    return updateRecord(memState.asRecord(), lval, rval, true);
  }
  
  protected RecordExpression updateAllocState(Expression allocState, Expression lval, Expression rval) {
    return updateRecord(allocState.asRecord(), lval, rval, false);
  }
  
  protected RecordExpression updateMemoryState(Expression memState) {
    return updateRecord(memState.asRecord(), true);
  }
  
  protected RecordExpression updateAllocState(Expression allocState) {
    return updateRecord(allocState.asRecord(), false);
  }
  
  private RecordExpression updateRecord(RecordExpression state, boolean mem) {
    Map<String, Expression> map = mem ? currentMemElems : currentAllocElems;
    if(map.isEmpty())   return state;
    
    map.putAll(getRecordElems(state));
    return getExpressionManager().record(getCurrentRecordType(mem), map.values());
  }
  
  private RecordExpression updateRecord(RecordExpression state, Expression lval, Expression rval, boolean mem) {
    Map<String, Expression> map = mem ? currentMemElems : currentAllocElems;
    boolean stateTypeChanged = !map.isEmpty();
    map.putAll(getRecordElems(state));
    
    ExpressionManager em = getExpressionManager();

    AliasVar lvalRepVar = loadRepVar(lval.getNode());    
    String lvalRepArrName = mem ? getMemArrElemName(lvalRepVar) : getAllocArrElemName(lvalRepVar);
    
    if(map.containsKey(lvalRepArrName)) {
      ArrayExpression lvalRepArr = map.get(lvalRepArrName).asArray();
//      Type cellType = lvalRepArr.getType().getElementType();
//      rval = castExprToCell(rval, cellType);
      lvalRepArr = lvalRepArr.update(lval, rval);
      map.put(lvalRepArrName, lvalRepArr);
    } else {
      xtc.type.Type lvalRepType = lvalRepVar.getType();
      Type cellType = getArrayElemType(lvalRepType);
      ArrayType arrType = em.arrayType(addrType, cellType);
      ArrayExpression lvalArr = em.variable(lvalRepArrName, arrType, false).asArray();
//      rval = castExprToCell(rval, cellType);
      lvalArr = lvalArr.update(lval, rval);
      map.put(lvalRepArrName, lvalArr);
      stateTypeChanged = true;
    }
    
    Type currentStateType = stateTypeChanged ? getCurrentRecordType(mem) : state.getType();
    return em.record(currentStateType, map.values());
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
   * Get the cell tyoe of the array in memory record for node with @param type
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
    Preconditions.checkArgument(memState.isRecord());
    currentMemElems.putAll(getRecordElems(memState.asRecord()));
  }
  
  private void initCurrentAllocElems(Expression allocState) {
    Preconditions.checkArgument(allocState.isRecord());
    currentAllocElems.putAll(getRecordElems(allocState.asRecord()));
  }
  
  private Map<String, Expression> getRecordElems(RecordExpression record) {
    Map<String, Expression> resMap = Maps.newLinkedHashMap();
    Iterable<String> elemNames = record.getType().getElementNames();
    Iterable<String> fieldNames = pickFieldNames(elemNames);
    assert(Iterables.size(elemNames) == Iterables.size(fieldNames));
    Iterator<String> elemNameItr = elemNames.iterator();
    Iterator<String> fieldNameItr = fieldNames.iterator();
    while(elemNameItr.hasNext() && fieldNameItr.hasNext()) {
      String elemName = elemNameItr.next();
      String fieldName = fieldNameItr.next();
      Expression value = record.select(elemName);
      resMap.put(fieldName, value);
    }
    return resMap;
  }
  
  private ImmutableList<ImmutableList<Expression>> getCategorizedVars(
      Iterable<AliasVar> equivVars) {
    ImmutableList.Builder<Expression> stVarsBuilder, stRegsBuilder, hpRegsBuilder;
    stVarsBuilder = new ImmutableList.Builder<Expression>();
    stRegsBuilder = new ImmutableList.Builder<Expression>();
    hpRegsBuilder = new ImmutableList.Builder<Expression>();
 
    for(AliasVar var : equivVars) {
      String varName = var.getName();
      String varScope = var.getScope();
      Pair<String, String> varKey = Pair.of(varName, varScope);
      if(CType.CONSTANT.equals(varName)) continue;
      if(lvals.containsKey(varKey)) {
        Expression expr = lvals.get(varKey);
        if(stackRegions.contains(expr)) {
          stRegsBuilder.add(expr);
        } else {
          stVarsBuilder.add(expr);
        }
      } else if(heapRegions.containsKey(varKey)) {
        hpRegsBuilder.add(heapRegions.get(varKey));
      } else {
        IOUtils.out().println("Variable " + varName + " @" + var.getScope() + " not yet be analyzed");
      }
    }
    
    ImmutableList.Builder<ImmutableList<Expression>> builder = 
        new ImmutableList.Builder<ImmutableList<Expression>>();
    builder.add(stVarsBuilder.build());
    builder.add(stRegsBuilder.build());
    builder.add(hpRegsBuilder.build());
    return builder.build();
  }
  
  private void setCurrentState(Expression state, Expression statePrime) {
    currentState = suspend(state, statePrime);
  }
  
  /**
   * Get the valid allocated assumption
   * @param allocated: indicate whether this method is called inside allocated. If true, the ptr node is
   * actually the region node, otherwise, the ptr node is like m[ptr], whose source node is ptr node
   * we need analyzer to get the points to node.
   */
  private BooleanExpression valid_malloc(Expression state, Expression ptr, Expression size, boolean allocated) {
    ExpressionManager exprManager = getExpressionManager();

    /* Find related heap regions and alloc array */
    AliasVar pRepVar = loadRepVar(ptr.getNode());
    if(!allocated) pRepVar = analyzer.getPointsToRepVar(pRepVar);
    
    Iterable<AliasVar> equivAliasVars = analyzer.getEquivClass(pRepVar);
    List<Expression> regions = Lists.newArrayListWithCapacity(Iterables.size(equivAliasVars));  
    
    for(AliasVar var : equivAliasVars) {
      Pair<String, String> varKey = Pair.of(var.getName(), var.getScope());
      if(heapRegions.containsKey(varKey)) {
        regions.add(heapRegions.get(varKey));
      }
    }
    
    initCurrentAllocElems(state.getChild(1));
    String allocArrName = getAllocArrElemName(pRepVar);
    assert currentAllocElems.containsKey(allocArrName);
    ArrayExpression allocArr = currentAllocElems.get(allocArrName).asArray();
    
    /* Build valid malloc assumption */
    
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    
    Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
    Expression sizeZro = exprManager.bitVectorZero(cellType.getSize());
    Expression ptrBound = exprManager.plus(addrType.getSize(), ptr, size);
    
    Expression assump = exprManager.neq(ptr, nullPtr);
    
    /* size not overflow */
    builder.add(exprManager.lessThan(ptr, ptrBound));
    
    /* Don't overlap any previously allocated and not freed HEAP region */   
    /* Collect all heap regions except the last one, the one just allocated. */
    regions.remove(regions.size()-1);
    
    for(Expression region : regions) {
      Expression regionSize = allocArr.index(region);
      Expression regionBound = exprManager.plus(addrType.getSize(), region, regionSize);
      
      /* region is not null and not freed before */
      Expression assump_local = exprManager.and( 
          exprManager.greaterThan(regionSize, sizeZro),
          region.neq(nullPtr));
      
      /* Disjoint */
      Expression assert_local = exprManager.or(
          exprManager.lessThanOrEqual(ptrBound, region),
          exprManager.lessThanOrEqual(regionBound, ptr));
      
      builder.add(exprManager.implies(assump_local, assert_local));
    }
    
    BooleanExpression res = exprManager.implies(assump, exprManager.and(builder.build()));
    
    return res;
  }
}
