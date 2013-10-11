package edu.nyu.cascade.ir.expr;

import java.util.Collection;
import java.util.List;
import java.util.Map;
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
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.ArrayType;
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

  private final Type addrType, valueType; // const type
  
  private final ArrayType sizeArrType; // ref-type -> off-type
  private RecordType memType; // with multiple array types
  private TupleType stateType;
  
  private static final String MIX_TYPE_NAME = "mix";
  private static final String PTR_CONSTR_NAME = "ptr";
  private static final String SCALAR_CONSTR_NAME = "scalar";
  private static final String PTR_SELECTOR_NAME = "ptr-sel";
  private static final String SCALAR_SELECTOR_NAME = "scalar-sel";
  
  private final HeapEncoding heapEncoding;
  
  private final InductiveType mixType; // The list inductive data type
  private final Constructor ptrConstr, scalarConstr; // The constructors for cell type
  private final Selector ptrSel, scalarSel; // The selectors for cell type
  
  private final Map<String, ArrayExpression> currentMemElems;
  
  private AliasAnalysis analyzer = null;
  private ArrayExpression currentSizeArr = null;
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
    heapEncoding = SynchronousHeapEncoding.create(encoding);
    
    valueType = heapEncoding.getValueType();
    addrType = heapEncoding.getAddressType();
    
    scalarSel = exprManager.selector(SCALAR_SELECTOR_NAME, valueType);
    scalarConstr = exprManager.constructor(SCALAR_CONSTR_NAME, scalarSel);
    
    ptrSel = exprManager.selector(PTR_SELECTOR_NAME, addrType);
    ptrConstr = exprManager.constructor(PTR_CONSTR_NAME, ptrSel);

    /* Create datatype */
    mixType = exprManager.dataType(MIX_TYPE_NAME, scalarConstr, ptrConstr);
    
    ImmutableList.Builder<String> elemNameBuilder = new ImmutableList.Builder<String>();
    ImmutableList.Builder<Type> elemTypeBuilder = new ImmutableList.Builder<Type>();
    memType = exprManager.recordType(
    		Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), 
        elemNameBuilder.build(), elemTypeBuilder.build());
    sizeArrType = heapEncoding.getSizeArrType();
    stateType = exprManager.tupleType(
        Identifiers.uniquify(DEFAULT_STATE_TYPE), memType, sizeArrType);
    
    currentMemElems = Maps.newLinkedHashMap();
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));

    ExpressionManager exprManager = getExpressionManager();
    
    AliasVar ptr_var = loadRepVar(ptr.getNode());
    AliasVar regionVar = analyzer.getAllocRegion(ptr_var);
    
    final String regionName = regionVar.getName();
    GNode regionNode = GNode.create("PrimaryIdentifier", regionName);
    regionVar.getType().mark(regionNode);
    final String regionScope = regionVar.getScope();
    regionNode.setProperty(CType.SCOPE, regionScope);
    
    Expression locVar = heapEncoding.freshRegion(regionName, regionNode);
    
    /* Update memory state */
    initCurrentMemElems(state.getChild(0));
    AliasVar regionRepVar = analyzer.getPointsToRepVar(ptr_var);
    
    { /* Add newly sizeArrated region array to current memory elements */
      String regionArrName = getArrayElemName(regionRepVar);
      if(!currentMemElems.containsKey(regionArrName)) {
        Type cellType = getArrayElemType(regionRepVar.getType());
        ArrayType arrType = exprManager.arrayType(addrType, cellType);
        ArrayExpression regionArr = exprManager.variable(regionArrName, arrType, false).asArray();
        currentMemElems.put(regionArrName, regionArr);
      }
    }
    
    { /* Update the pointer array in current memory elements */  
      String ptrRepArrName = getArrayElemName(ptr_var);
      if(currentMemElems.containsKey(ptrRepArrName)) {
        ArrayExpression ptrRepArr = currentMemElems.get(ptrRepArrName);
        Type cellType = ptrRepArr.getType().getElementType();
        Expression locVarPrime = castExprToCell(locVar, cellType);
        ptrRepArr = ptrRepArr.update(ptr, locVarPrime);
        currentMemElems.put(ptrRepArrName, ptrRepArr);
      } else {
        xtc.type.Type ptrRepVarType = ptr_var.getType();
        CellKind ptrRepVarKind = CType.getCellKind(ptrRepVarType);
        
        Type cellType = CellKind.POINTER.equals(ptrRepVarKind) ? addrType : valueType;
        ArrayType arrType = exprManager.arrayType(addrType, cellType);
        ArrayExpression ptrRepArr = exprManager.variable(ptrRepArrName, arrType, false).asArray();
        assert(cellType.equals(locVar.getType()));
        ptrRepArr = ptrRepArr.update(ptr, locVar);
        currentMemElems.put(ptrRepArrName, ptrRepArr);
      }
    } 
    
    Type memPrimeType = getRecordTypeFromMap(
    		Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), currentMemElems);
    Expression memPrime = exprManager.record(memPrimeType, currentMemElems.values());
    
    Expression sizeArrPrime = heapEncoding.updateSizeArr(state.getChild(1).asArray(), locVar, size);    
    TupleExpression statePrime = getUpdatedState(state, memPrime, sizeArrPrime);
    setStateType(statePrime.getType());
    
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));
    
    Expression sizeArr = heapEncoding.updateSizeArr(state.getChild(1).asArray(), ptr, size);
    return getUpdatedState(state, state.getChild(0), sizeArr);
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));
    
    Expression sizeArr = heapEncoding.updateSizeArr(state.getChild(1).asArray(), ptr, size);    
    return getUpdatedState(state, state.getChild(0), sizeArr);
  }
  
  @Override
  public TupleExpression free(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( addrType )); 
    
    Expression sizeZero = heapEncoding.getValueZero();
    Expression sizeArr = heapEncoding.updateSizeArr(state.getChild(1).asArray(), ptr, sizeZero);
    return getUpdatedState(state, state.getChild(0), sizeArr);
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
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression pValCell = null;
    AliasVar pRepVar = loadRepVar(p.getNode());
    
    String pArrName = getArrayElemName(pRepVar);
    if(currentMemElems.containsKey(pArrName)) {
      ArrayExpression pArray = currentMemElems.get(pArrName).asArray();
      pValCell = pArray.index(p);
    } else { // Add an element to currentMemElem
      Type cellType = getArrayElemType(pRepVar.getType());
        
      ArrayType arrType = exprManager.arrayType(addrType, cellType);
      ArrayExpression pArray = exprManager.variable(pArrName, arrType, false).asArray();
      currentMemElems.put(pArrName, pArray);
      pValCell = pArray.index(p);
      
      Type memPrimeType = getRecordTypeFromMap(
      		Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), currentMemElems);
      Expression memPrime = exprManager.record(memPrimeType, currentMemElems.values());
      if(currentSizeArr == null)    currentSizeArr = state.getChild(1).asArray();
      Expression statePrime = getUpdatedState(state, memPrime, currentSizeArr);
      currentState = suspend(state, statePrime);    
    }
    
    if(mixType.equals(pValCell.getType())) {
      CellKind kind = CType.getCellKind(CType.unwrapped(CType.getType(p.getNode())));
      switch(kind) {
      case SCALAR:
      case BOOL:
        pValCell = exprManager.select(scalarSel, pValCell); break;
      case POINTER:
        pValCell = exprManager.select(ptrSel, pValCell); break;
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
    Preconditions.checkArgument(lval.getType().equals( addrType ));
    Expression rval = null;
    
    CellKind kind = CType.getCellKind(CType.getType(lval.getNode()));
    switch(kind) {
    case POINTER: rval = getExpressionEncoding().getPointerEncoding().unknown(); break;
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
    
    Expression res = heapEncoding.freshAddress(prefix+name, node);
    return res;
  }
  
  @Override
  public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));

    AliasVar repVar = loadRepVar(ptr.getNode());
    analyzer.heapAssign(repVar, CType.getType(ptr.getNode()));
    IOUtils.debug().pln(analyzer.displaySnapShort());
    AliasVar regionVar = analyzer.getAllocRegion(repVar);
    
    String regionName = regionVar.getName();
    GNode regionNode = GNode.create("PrimaryIdentifier", regionName);
    regionVar.getType().mark(regionNode);
    regionNode.setProperty(CType.SCOPE, regionVar.getScope());
    
    Expression locVar = heapEncoding.freshRegion(regionName, regionNode);
    
    Expression currentMem = updateMemoryState(state.getChild(0), ptr, locVar);
    
    if(currentSizeArr == null)    currentSizeArr = state.getChild(1).asArray();
    currentSizeArr = heapEncoding.updateSizeArr(currentSizeArr, locVar, size);

    Expression statePrime = getUpdatedState(state, currentMem, currentSizeArr);
    currentState = suspend(state, statePrime);
    
    return valid_malloc(state, locVar, size);
  }
  
  @Override
  public Expression addressOf(Expression content) {    
    if(Kind.APPLY.equals(content.getKind())) {
      return content.getChild(0).getChild(1);
    } else {
      CellKind kind = CType.getCellKind(CType.getType(content.getNode()));
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
          "--order-sizeArr is not supported in partition memory model");
    }
    
    if (Preferences.isSet(Preferences.OPTION_SOUND_ALLOC))
    	return heapEncoding.disjointMemLayoutSound();
      	
    return null;
  }

  @Override
  public Expression freshState() {
    ExpressionManager exprManager = getExpressionManager();
    Expression memVar = exprManager.variable(DEFAULT_MEMORY_VARIABLE_NAME, 
        memType, true);
    Expression sizeArrVar = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, 
        sizeArrType, true);
    return exprManager.tuple(stateType, memVar, sizeArrVar);
  }
  
  @Override
  public RecordType getMemoryType() {
    return memType;
  }
  
  @Override
  public ArrayType getAllocType() {
    return sizeArrType;
  }
  
  @Override
  public TupleType getStateType() {
    return stateType;
  }
  
  @Override
  public boolean setStateType(Type stateType) {
  	Preconditions.checkArgument(stateType.isTuple());
  	if(this.stateType.equals(stateType))	return false;
    this.stateType = stateType.asTuple();
    this.memType = stateType.asTuple().getElementTypes().get(0).asRecord();
    return true;
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
          
          Map<String, ArrayExpression> memVarMemMap = getRecordElems(memVar_mem);
          Map<String, ArrayExpression> memoryMemMap = getRecordElems(memory_mem);
          
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
          
          /* Substitute the sizeArr of expr */
          Expression memVar_sizeArr = memoryVar.getChild(1);
          Expression memory_sizeArr = memory.getChild(1);
          
          exprPrime = exprPrime.subst(memVar_sizeArr, memory_sizeArr);          
          return exprPrime.setNode(expr.getNode());
        } else {
          /* For tuple expression evaluation over memoryVar, since substitution doesn't return
           * right children for as tuple expression for state.
           */
          ExpressionManager exprManager = getExpressionManager();
          
          Expression memory_mem = memory.getChild(0);
          Expression memory_sizeArr = memory.getChild(1);
          
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
            elem = elem.subst(memoryVar.getChild(1), memory_sizeArr);
            elemMap.put(name, elem);
          }
          
          Expression memPrime = exprManager.record(expr_mem_type, elemMap.values());
          
          /* Substitute the sizeArr of expr to sizeArrPrime */
          Expression sizeArrPrime = null;
          
          Expression sizeArr = expr.getChild(1);
          if(sizeArr.isVariable()) { // substitution makes no effect for variable
            assert(sizeArr.equals(memoryVar.getChild(1)));
            sizeArrPrime = memory.getChild(1);
          } else {
            sizeArrPrime = sizeArr.subst(memoryVar.getChild(0), memory_mem);
            sizeArrPrime = sizeArr.subst(memoryVar.getChild(1), memory_sizeArr);
          }
          
          /* Update memType, sizeArrType and stateType -- static member of memory model */
          setStateType(expr.getType().asTuple());
          
          return exprManager.tuple(expr.getType(), memPrime, sizeArrPrime);
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
    currentSizeArr = null;
    currentState = null;
  }
  
  private RecordExpression updateMemoryState(Expression memState, Expression lval, Expression rval) {
    initCurrentMemElems(memState);
    
    ExpressionManager exprManager = getExpressionManager();
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
      ArrayType arrType = exprManager.arrayType(addrType, cellType);
      ArrayExpression lvalArr = exprManager.variable(lvalRepArrName, arrType, false).asArray();
      rval = castExprToCell(rval, cellType);
      lvalArr = lvalArr.update(lval, rval);
      currentMemElems.put(lvalRepArrName, lvalArr);
      isMemUpdated = true;
    }
    
    Type currentMemType = isMemUpdated? getRecordTypeFromMap(
    		Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), currentMemElems) 
    		: memState.getType();
    return exprManager.record(currentMemType, currentMemElems.values());
  }
  
  @Override
  public void setAliasAnalyzer(AliasAnalysis analyzer) {
    this.analyzer = analyzer;
    IOUtils.debug().pln(analyzer.displaySnapShort());
  }
  
  /**
   * Recreate state from @param memoryPrime and @param sizeArrPrime and create a new state
   * type if state type is changed from the type of state
   * @return a new state
   */
  public TupleExpression getUpdatedState(Expression state, Expression memoryPrime, Expression sizeArrPrime) {
    ExpressionManager exprManager = getExpressionManager();
    Type stateTypePrime = null;
    
    if(state != null 
        && state.getType().asTuple().getElementTypes().get(0).equals(memoryPrime.getType())) {
      stateTypePrime = state.getType();
    } else {
      stateTypePrime = exprManager.tupleType(Identifiers.uniquify(DEFAULT_STATE_TYPE), 
          memoryPrime.getType(), sizeArrPrime.getType());
    }
    
    return exprManager.tuple(stateTypePrime, memoryPrime, sizeArrPrime);
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    
    Collection<BooleanExpression> res = heapEncoding.validMemAccess(
    		state.getChild(1).asArray(), ptr);
    
    return getExpressionManager().or(res);
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));
    
    Collection<BooleanExpression> res = heapEncoding.validMemAccess(
    		state.getChild(1).asArray(), ptr, size);

    return getExpressionManager().or(res);
  }
  
  @Override
  public BooleanExpression valid_malloc(Expression state, Expression ptr, Expression size) {
    ExpressionManager exprManager = getExpressionManager();
    
    if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
      throw new UnsupportedOperationException(
          "--order-sizeArr is not supported in partition memory model");
    } 
    
    if (Preferences.isSet(Preferences.OPTION_SOUND_ALLOC)) {
    	
      /* Only analyze heap part. 
       * Collect all heap regions except the last one, the one just sizeArrated. 
       */
      return heapEncoding.validMallocSound(state.getChild(1).asArray(), ptr, size);
    }
    
    return exprManager.tt();
  }
  
  @Override
  public BooleanExpression valid_free(Expression state, Expression ptr) {
  	return heapEncoding.validFree(state.getChild(1).asArray(), ptr);
  }
  
  @Override
  public Expression substAlloc(Expression expr) {
    ExpressionManager exprManager = getExpressionManager();
    Expression initialSizeArr = exprManager.variable(DEFAULT_ALLOC_VARIABLE_NAME, sizeArrType, false);
    Expression constSizeArr = heapEncoding.getConstSizeArr(sizeArrType);
    Expression res = expr.subst(initialSizeArr, constSizeArr);
    return res;
  }
    
  /**
   * Get representative alias variable in the pointer analyzer
   * @param gnode
   */
  private AliasVar getRepVar(GNode gnode) {
    xtc.type.Type type = CType.getType(gnode);
    String scope = CType.getScope(gnode);
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
      String scope = CType.getScope(gnode);
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
    
    if(valueType.equals(rval.getType())) {
      if(addrType.equals(cellType)) {
        xtc.type.Type type = CType.getType(rval.getNode());
        assert type.hasConstant() ;
        Constant constant =  type.getConstant();
        
        if(constant.isNumber() && constant.bigIntValue().intValue() == 0) {
          return getExpressionEncoding().getPointerEncoding().getNullPtr();
        }
        
        if(constant.isReference()) {
          assert ((Reference) constant.getValue()).isCast();
          CastReference ref = (CastReference) constant.getValue();
          if(ref.getBase().isNull()) {
            return getExpressionEncoding().getPointerEncoding().getNullPtr();
          }
        }
        
        return getExpressionEncoding().getPointerEncoding().unknown();
      } 
      
      if(mixType.equals(cellType)) {
        return exprManager.construct(scalarConstr, rval);
      }
    } else if(addrType.equals(rval.getType())) {
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
    case BOOL :     cellType = valueType; break;
    case ARRAY : {
      xtc.type.Type contentType = CType.unwrapped(type).toArray().getType();
      cellType = getArrayElemType(contentType);
      break;
    }
    case POINTER :  cellType = addrType; break;
    case STRUCTORUNION : {
      ElemType elemType = getElemType(type);
      switch(elemType) {
      case SCALAR:  cellType = valueType; break;
      case POINTER: cellType = addrType; break;
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
