package edu.nyu.cascade.ir.expr;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Iterator;
import java.util.concurrent.ExecutionException;

import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.type.CastReference;
import xtc.type.Constant;
import xtc.type.Reference;
import xtc.type.StructOrUnionT;
import xtc.type.VariableT;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.c.preprocessor.AliasAnalysis;
import edu.nyu.cascade.c.preprocessor.AliasVar;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.Expression.Kind;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.Selector;
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

public class PartitionMemoryModelObject extends AbstractMemoryModel {

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static PartitionMemoryModelObject create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new PartitionMemoryModelObject(encoding);
  }

  private static final String ARRAY_PREFIX = "arr_of_";

  private final TupleType ptrType; // pointer type = (ref-type, off-type)
  private final Type refType;
  private final BitVectorType scalarType, offType; // const type
  
  private final ArrayType allocType; // ref-type -> off-type
  private RecordType memType; // with multiple array types
  private TupleType stateType;
  
  private static final String MIX_TYPE_NAME = "mix";
  private static final String PTR_CONSTR_NAME = "ptr";
  private static final String SCALAR_CONSTR_NAME = "scalar";
  private static final String PTR_SELECTOR_NAME = "ptr-sel";
  private static final String SCALAR_SELECTOR_NAME = "scalar-sel";
  
  private final InductiveType mixType; // The list inductive data type
  private final Constructor ptrConstr, scalarConstr; // The constructors for cell type
  private final Selector ptrSel, scalarSel; // The selectors for cell type
  
  private final Set<Expression> lvals; // lvals: variables in stack
  private final List<Expression> heapRegions;
  private final Map<String, Expression> currentMemElems;
  
  private AliasAnalysis analyzer = null;
  private Expression currentAlloc = null;
  private Expression prevDerefState = null;
  private ExpressionClosure currentState = null;
  
  private final LoadingCache<Pair<GNode, String>, AliasVar> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<Pair<GNode, String>, AliasVar>(){
        public AliasVar load(Pair<GNode, String> key) {
          return getRepVar(key.fst());
        }
      });
  
  private enum ElemType {
    SCALAR,
    POINTER,
    MIX
  }

  private PartitionMemoryModelObject(ExpressionEncoding encoding) {
    super(encoding);
    
    ExpressionManager exprManager = getExpressionManager();
    
    int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
    this.scalarType = exprManager.bitVectorType(size);
    this.ptrType = ((PointerExpressionEncoding) encoding).getPointerEncoding().getType();
    
    scalarSel = exprManager.selector(SCALAR_SELECTOR_NAME, scalarType);
    scalarConstr = exprManager.constructor(SCALAR_CONSTR_NAME, scalarSel);
    
    ptrSel = exprManager.selector(PTR_SELECTOR_NAME, ptrType);
    ptrConstr = exprManager.constructor(PTR_CONSTR_NAME, ptrSel);

    /* Create datatype */
    this.mixType = exprManager.dataType(MIX_TYPE_NAME, scalarConstr, ptrConstr);
    
    this.refType = ptrType.getElementTypes().get(0);
    this.offType = ptrType.getElementTypes().get(1).asBitVectorType();
    
    List<String> elemNames = Lists.newArrayList();
    List<Type> elemTypes = Lists.newArrayList();
    this.memType = exprManager.recordType(
        Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), 
        elemNames, elemTypes);
    this.allocType = exprManager.arrayType(refType, offType);
    this.stateType = exprManager.tupleType(
        Identifiers.uniquify(DEFAULT_STATE_TYPE), memType, allocType);
    
    this.lvals = Sets.newHashSet();
    this.heapRegions = Lists.newArrayList();
    
    this.currentMemElems = Maps.newLinkedHashMap();
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    Preconditions.checkArgument(size.getType().equals( offType ));

    ExpressionManager em = getExpressionManager();
    
    AliasVar ptr_var = loadRepVar(ptr.getNode());
    AliasVar regionVar = analyzer.getAllocRegion(ptr_var);
    
    String regionName = regionVar.getName();
    Expression refVar = em.variable(regionName, refType, false);
    Expression offZero = em.bitVectorZero(offType.getSize());
    Expression locVar = em.tuple(ptrType, refVar, offZero);
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end
    
    /* Update memory state */
    initCurrentMemElems(state.getChild(0));
    AliasVar regionRepVar = analyzer.getPointsToRepVar(ptr_var);
    
    { /* Add newly allocated region array to current memory elements */
      String regionArrName = getArrayElemName(regionRepVar);
      if(!currentMemElems.containsKey(regionArrName)) {
        Type cellType = getArrayElemType(regionRepVar.getType());
        ArrayType arrType = em.arrayType(ptrType, cellType);
        ArrayExpression regionArr = em.variable(regionArrName, arrType, false).asArray();
        currentMemElems.put(regionArrName, regionArr);
      }
    }
    
    { /* Update the pointer array in current memory elements */  
      String ptrRepArrName = getArrayElemName(ptr_var);
      if(currentMemElems.containsKey(ptrRepArrName)) {
        ArrayExpression ptrRepArr = currentMemElems.get(ptrRepArrName).asArray();
        Type cellType = ptrRepArr.getType().getElementType();
        locVar = castExprToCell(locVar, cellType);
        ptrRepArr = ptrRepArr.update(ptr, locVar);
        currentMemElems.put(ptrRepArrName, ptrRepArr);
      } else {
        xtc.type.Type ptrRepVarType = ptr_var.getType();
        CellKind ptrRepVarKind = CType.getCellKind(ptrRepVarType);
        
        Type cellType = CellKind.POINTER.equals(ptrRepVarKind) ? ptrType : scalarType;
        ArrayType arrType = em.arrayType(ptrType, cellType);
        ArrayExpression ptrRepArr = em.variable(ptrRepArrName, arrType, false).asArray();
        assert(cellType.equals(locVar.getType()));
        ptrRepArr = ptrRepArr.update(ptr, locVar);
        currentMemElems.put(ptrRepArrName, ptrRepArr);
      }
    } 
    
    Type memPrimeType = getRecordTypeFromMap(
    		Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), currentMemElems);
    Expression memPrime = em.record(memPrimeType, currentMemElems.values());
    Expression alloc = state.getChild(1).asArray().update(refVar, size);    
    TupleExpression statePrime = getUpdatedState(state, memPrime, alloc);
    setStateType(statePrime.getType());
    
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    /* Cannot use stackRegion = ptr.getChild(0), ptr.getChild(0) = m */
    Expression stackRegion = ptr.asTuple().index(0);
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size);
    return getUpdatedState(state, state.getChild(0), alloc);
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    /* Cannot use stackRegion = ptr.getChild(0), ptr.getChild(0) = m */
    Expression stackRegion = ptr.asTuple().index(0);
    Expression alloc = state.getChild(1).asArray().update(stackRegion, size);
    
    return getUpdatedState(state, state.getChild(0), alloc);
  }
  
  @Override
  public TupleExpression free(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType )); 
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression sizeZero = exprManager.bitVectorZero(offType.getSize());
    Expression alloc = state.getChild(1);
    
    try {
      for( Expression locVar : heapRegions )
        alloc = exprManager.ifThenElse(ptr.asTuple().index(0).eq(locVar), 
            alloc.asArray().update(locVar, sizeZero), alloc);
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return getUpdatedState(state, state.getChild(0), alloc);
  }

  @Override
  public TupleExpression assign(
      Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    RecordExpression memory = updateMemoryState(state.getChild(0), lval, rval);
    TupleExpression statePrime = getUpdatedState(state, memory, state.getChild(1));
    setStateType(statePrime.getType());
    
    return statePrime;
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    Preconditions.checkArgument(ptrType.equals(p.getType()));
    
    // Initialization
    if(currentMemElems.isEmpty() || state != prevDerefState) {
      initCurrentMemElems(state.getChild(0));
      prevDerefState = state;
    }
    
    ExpressionManager em = getExpressionManager();
    
    Expression pValCell = null;
    AliasVar pRepVar = loadRepVar(p.getNode());
    
    String pArrName = getArrayElemName(pRepVar);
    if(currentMemElems.containsKey(pArrName)) {
      ArrayExpression pArray = currentMemElems.get(pArrName).asArray();
      pValCell = pArray.index(p);
    } else { // Add an element to currentMemElem
      Type cellType = getArrayElemType(pRepVar.getType());
        
      ArrayType arrType = em.arrayType(ptrType, cellType);
      ArrayExpression pArray = em.variable(pArrName, arrType, false).asArray();
      currentMemElems.put(pArrName, pArray);
      pValCell = pArray.index(p);
      
      Type memPrimeType = getRecordTypeFromMap(
      		Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), currentMemElems);
      Expression memPrime = em.record(memPrimeType, currentMemElems.values());
      if(currentAlloc == null)    currentAlloc = state.getChild(1);
      Expression statePrime = getUpdatedState(state, memPrime, currentAlloc);
      currentState = suspend(state, statePrime);    
    }
    
    if(mixType.equals(pValCell.getType())) {
      CellKind kind = CType.getCellKind(CType.unwrapped((xtc.type.Type) p.getNode().getProperty(TYPE)));
      switch(kind) {
      case SCALAR:
      case BOOL:
        pValCell = em.select(scalarSel, pValCell); break;
      case POINTER:
        pValCell = em.select(ptrSel, pValCell); break;
      default:
        throw new IllegalArgumentException("Invalid kind " + kind);
      }
    }
    return pValCell;
  }
  
  @Override
  public TupleExpression havoc(
      Expression state,
      Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( ptrType ));
    Expression rval = null;
    
    xtc.type.Type lvalType = (xtc.type.Type) lval.getNode().getProperty(TYPE);
    CellKind kind = CType.getCellKind(lvalType);
    switch(kind) {
    case POINTER: rval = getExpressionEncoding().unknown(); break;
    case SCALAR:  rval = getExpressionEncoding().getIntegerEncoding().unknown(); break;
    case BOOL:    rval = getExpressionEncoding().getIntegerEncoding().unknown(); break;
    default: throw new IllegalArgumentException("Invalid kind " + kind);
    }
    RecordExpression memory = updateMemoryState(state.getChild(0), lval, rval); 
    TupleExpression statePrime = getUpdatedState(state, memory, state.getChild(1));
    setStateType(statePrime.getType());
        
    return statePrime;
  }
  
  @Override
  public Expression createLval(String prefix, Node node) {
    Preconditions.checkArgument(node.hasName("PrimaryIdentifier") 
        || node.hasName("SimpleDeclarator"));
    String name = node.getString(0);
    ExpressionManager exprManager = getExpressionManager();
    VariableExpression ref = exprManager.variable(prefix+name, refType, true);
    Expression off = exprManager.bitVectorZero(offType.getSize());
    Expression res = exprManager.tuple(ptrType, ref, off);
    lvals.add(ref);
    return res;
  }
  
  @Override
  public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    ExpressionManager exprManager = getExpressionManager();

    AliasVar repVar = loadRepVar(ptr.getNode());
    analyzer.heapAssign(repVar, (xtc.type.Type) ptr.getNode().getProperty(TYPE));
    IOUtils.debug().pln(analyzer.displaySnapShort());
    AliasVar regionVar = analyzer.getAllocRegion(repVar);
    
    String regionName = regionVar.getName();
    Expression refVar = exprManager.variable(regionName, refType, false);
    Expression offZero = exprManager.bitVectorZero(offType.getSize());
    Expression locVar = exprManager.tuple(ptrType, refVar, offZero);
    heapRegions.add(refVar); // For dynamic memory allocation, add to the end
    
    Expression currentMem = updateMemoryState(state.getChild(0), ptr, locVar);
    
    if(currentAlloc == null)    currentAlloc = state.getChild(1);
    currentAlloc = currentAlloc.asArray().update(refVar, size);

    Expression statePrime = getUpdatedState(state, currentMem, currentAlloc);
    currentState = suspend(state, statePrime);
    
    return valid_malloc(state, locVar, size);
  }
  
  @Override
  public Expression addressOf(Expression content) {
    Preconditions.checkArgument(content.getNode().hasProperty(TYPE));
    
    if(Kind.APPLY.equals(content.getKind())) {
      return content.getChild(0).getChild(1);
    } else {
      xtc.type.Type contentType = (xtc.type.Type) (content.getNode().getProperty(TYPE));
      CellKind kind = CType.getCellKind(contentType);
      switch(kind) {
      case STRUCTORUNION: 
      case ARRAY:   return content;
      default:      return content.getChild(1);
      }
    }
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
      if (Preferences.isSet(Preferences.OPTION_SOUND_ALLOC)) {
        ExpressionManager exprManager = getExpressionManager();
        
        { /* The disjointness of stack variables, and != nullRef*/
          Expression nullRef = ((PointerExpressionEncoding) getExpressionEncoding())
              .getPointerEncoding().nullPtr().getChild(0);
          ImmutableList<Expression> distinctRef = new ImmutableList.Builder<Expression>()
              .addAll(lvals).add(nullRef).build();
          if(distinctRef.size() > 1)  builder.add(exprManager.distinct(distinctRef));
        }
        
        { /* The disjointness between heap region and stack variable. */
          for(Expression heapRegion : heapRegions) {
            for(Expression lval : lvals) {
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
  public ArrayType getAllocType() {
    return allocType;
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
          
          Map<String, Expression> memVarMemMap = getRecordElems(memVar_mem);
          Map<String, Expression> memoryMemMap = getRecordElems(memory_mem);
          
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
          
          exprPrime = exprPrime.subst(memVar_alloc, memory_alloc);          
          return exprPrime.setNode(expr.getNode());
        } else {
          /* For tuple expression evaluation over memoryVar, since substitution doesn't return
           * right children for as tuple expression for state.
           */
          ExpressionManager exprManager = getExpressionManager();
          
          Expression memory_mem = memory.getChild(0);
          Expression memory_alloc = memory.getChild(1);
          
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
          
          Expression memPrime = exprManager.record(expr_mem_type, elemMap.values());
          
          /* Substitute the alloc of expr to allocPrime */
          Expression allocPrime = null;
          
          Expression alloc = expr.getChild(1);
          if(alloc.isVariable()) { // substitution makes no effect for variable
            assert(alloc.equals(memoryVar.getChild(1)));
            allocPrime = memory.getChild(1);
          } else {
            allocPrime = alloc.subst(memoryVar.getChild(0), memory_mem);
            allocPrime = alloc.subst(memoryVar.getChild(1), memory_alloc);
          }
          
          /* Update memType, allocType and stateType -- static member of memory model */
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
    currentAlloc = null;
    currentState = null;
  }
  
  private RecordExpression updateMemoryState(Expression memState, Expression lval, Expression rval) {
    initCurrentMemElems(memState);
    
    ExpressionManager em = getExpressionManager();
    boolean isMemUpdated = false;

    AliasVar lvalRepVar = loadRepVar(lval.getNode());
    xtc.type.Type lvalRepType = lvalRepVar.getType();
    
    String lvalRepArrName = getArrayElemName(lvalRepVar);
    if(currentMemElems.containsKey(lvalRepArrName)) {
      ArrayExpression lvalRepArr = currentMemElems.get(lvalRepArrName).asArray();
      Type cellType = lvalRepArr.getType().getElementType();
      rval = castExprToCell(rval, cellType);
      lvalRepArr = lvalRepArr.update(lval, rval);
      currentMemElems.put(lvalRepArrName, lvalRepArr);
    } else {
      Type cellType = getArrayElemType(lvalRepType);
      ArrayType arrType = em.arrayType(ptrType, cellType);
      ArrayExpression lvalArr = em.variable(lvalRepArrName, arrType, false).asArray();
      rval = castExprToCell(rval, cellType);
      lvalArr = lvalArr.update(lval, rval);
      currentMemElems.put(lvalRepArrName, lvalArr);
      isMemUpdated = true;
    }
    
    Type currentMemType = isMemUpdated? getRecordTypeFromMap(
    		Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), currentMemElems) 
    		: memState.getType();
    return em.record(currentMemType, currentMemElems.values());
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
        && state.getType().asTuple().getElementTypes().get(0).equals(memoryPrime.getType())) {
      stateTypePrime = state.getType();
    } else {
      stateTypePrime = em.tupleType(Identifiers.uniquify(DEFAULT_STATE_TYPE), 
          memoryPrime.getType(), allocPrime.getType());
    }
    
    return em.tuple(stateTypePrime, memoryPrime, allocPrime);
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    
    List<BooleanExpression> disjs = Lists.newArrayList();
    
    try {
      ExpressionManager exprManager = getExpressionManager();
      Expression alloc = state.getChild(1);
      Expression ref_ptr = ptr.asTuple().index(0);
      Expression off_ptr = ptr.asTuple().index(1);
      Expression sizeZro = exprManager.bitVectorZero(offType.getSize());
      Expression nullRef = ((PointerExpressionEncoding) getExpressionEncoding())
          .getPointerEncoding().nullPtr().asTuple().getChild(0);
      
      // Valid stack access
      for( Expression lval : lvals) {
        Expression sizeVar = alloc.asArray().index(lval);
        disjs.add(
            exprManager.and(
                ref_ptr.eq(lval), 
                /* aggregate variable: size > 0; scalar variable: size = 0 */
                exprManager.ifThenElse( 
                    exprManager.greaterThan(sizeVar, sizeZro),
                    exprManager.and(
                        exprManager.greaterThanOrEqual(off_ptr, sizeZro),
                        exprManager.lessThan(off_ptr, sizeVar)),
                    off_ptr.eq(sizeVar))));
      }
      
      // Valid heap access
      for( Expression refVar : heapRegions ) {
        /* ptr:(ref_ptr, off), startPos:(ref, 0), endPos:(ref, size);
         * ensure ref_ptr == ref && 0 <= off && off < size
         */
        Expression sizeVar = alloc.asArray().index(refVar);
        disjs.add(
            exprManager.and(
                refVar.neq(nullRef),
                ref_ptr.eq(refVar),
                exprManager.lessThanOrEqual(sizeZro, off_ptr),
                exprManager.lessThan(off_ptr, sizeVar)));
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return getExpressionManager().or(disjs);
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( ptrType ));
    Preconditions.checkArgument(size.getType().equals( offType ));
    
    List<BooleanExpression> disjs = Lists.newArrayList();
    
    try {
      ExpressionManager exprManager = getExpressionManager();
      Expression alloc = state.getChild(1);
      Expression ref_ptr = ptr.asTuple().index(0);
      Expression off_ptr = ptr.asTuple().index(1);
      Expression off_bound = exprManager.plus(offType.getSize(), off_ptr, size);
      Expression sizeZro = exprManager.bitVectorZero(offType.getSize());
      Expression nullRef = ((PointerExpressionEncoding) getExpressionEncoding())
          .getPointerEncoding().nullPtr().asTuple().getChild(0);
      
      // Valid stack access
      for( Expression lval : lvals) {
        Expression sizeVar = alloc.asArray().index(lval);
        disjs.add(
            exprManager.and(
                ref_ptr.eq(lval), 
                /* aggregate variable: size > 0; scalar variable: size = 0 */
                exprManager.ifThenElse( 
                    exprManager.greaterThan(sizeVar, sizeZro),
                    exprManager.and(        
                        exprManager.greaterThanOrEqual(off_ptr, sizeZro),
                        exprManager.lessThan(off_bound, sizeVar)),
                    off_ptr.eq(sizeVar)))); 
      }
      
      // Valid heap access
      for( Expression refVar : heapRegions ) {
        Expression sizeVar = alloc.asArray().index(refVar);
        /* ptr:(ref_ptr, off), startPos:(ref, 0), endPos:(ref, size);
         * ensure ref_ptr == ref && 0 <= off && off < size
         */
        disjs.add(
            exprManager.and(
                refVar.neq(nullRef),
                ref_ptr.eq(refVar), 
                exprManager.lessThanOrEqual(sizeZro, off_ptr),
                exprManager.lessThan(off_bound, sizeVar)));
      }
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
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
      Expression sizeZro = exprManager.bitVectorZero(offType.getSize());
      
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
    ExpressionManager exprManager = getExpressionManager();
    Expression alloc = state.getChild(1); 
    Expression ref = ptr.asTuple().index(0);
    Expression size = alloc.asArray().index(ref);
    Expression nullPtr = ((PointerExpressionEncoding) getExpressionEncoding())
        .getPointerEncoding().nullPtr();
    return exprManager.or(exprManager.eq(ptr, nullPtr), exprManager.greaterThan(size, 
        exprManager.bitVectorZero(offType.getSize())));
  }
  
  @Override
  public Expression substAlloc(Expression expr) {
    ExpressionManager exprManager = getExpressionManager();
    Expression initialAlloc = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, allocType, false);
    Expression constAlloc = exprManager.storeAll(exprManager.bitVectorZero(offType.getSize()), allocType);
    Expression res = expr.subst(initialAlloc, constAlloc);
    return res;
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
  
  private ElemType getElemType(xtc.type.Type type) {
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
  }
  
  private Expression castExprToCell(Expression rval, Type cellType) {
    if(rval.getType().equals(cellType)) return rval;
    
    ExpressionManager exprManager = getExpressionManager();
    
    if(scalarType.equals(rval.getType())) {
      if(ptrType.equals(cellType)) {
        xtc.type.Type type = (xtc.type.Type) rval.getNode().getProperty(TYPE);
        assert type.hasConstant() ;
        Constant constant =  type.getConstant();
        
        if(constant.isNumber() && constant.bigIntValue().intValue() == 0) {
          return ((PointerExpressionEncoding) getExpressionEncoding())
              .getPointerEncoding().nullPtr();
        }
        
        if(constant.isReference()) {
          assert ((Reference) constant.getValue()).isCast();
          CastReference ref = (CastReference) constant.getValue();
          if(ref.getBase().isNull()) {
            return ((PointerExpressionEncoding) getExpressionEncoding())
                .getPointerEncoding().nullPtr();
          }
        }
        
        return getExpressionEncoding().unknown();
      } 
      
      if(mixType.equals(cellType)) {
        return exprManager.construct(scalarConstr, rval);
      }
    } else if(ptrType.equals(rval.getType())) {
      if(mixType.equals(cellType)) {
        return exprManager.construct(ptrConstr, rval);
      }
    }
    
    throw new IllegalArgumentException("Invalid type " + rval.getType() + " to " + cellType);
  }
  
  private String getArrayElemName(AliasVar var) {
    StringBuilder sb = new StringBuilder();
    sb.append(ARRAY_PREFIX).append(var.getName()).append('_').append(var.getScope());
    return Identifiers.toValidId(sb.toString());
  }
  
  /**
   * Get the cell tyoe of the array in memory record for node with certain type
   * @param type
   */
  private Type getArrayElemType(xtc.type.Type type) {
    Type cellType = null;
    switch(CType.getCellKind(type)) {
    case SCALAR :
    case BOOL :     cellType = scalarType; break;
    case ARRAY : {
      xtc.type.Type contentType = CType.unwrapped(type).toArray().getType();
      cellType = getArrayElemType(contentType);
      break;
    }
    case POINTER :  cellType = ptrType; break;
    case STRUCTORUNION : {
      ElemType elemType = getElemType(type);
      switch(elemType) {
      case SCALAR:  cellType = scalarType; break;
      case POINTER: cellType = ptrType; break;
      default:      cellType = mixType; 
      }
      break;
    }
    default:    throw new IllegalArgumentException("Unsupported type " + type);
    }
    return cellType;
  }
  
  private void initCurrentMemElems(Expression memState) {
    currentMemElems.putAll(getRecordElems(memState));
  }
}