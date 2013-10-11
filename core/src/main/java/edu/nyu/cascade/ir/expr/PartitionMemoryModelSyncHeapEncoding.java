package edu.nyu.cascade.ir.expr;

import java.util.Collection;
import java.util.Collections;
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
import com.google.common.base.Predicate;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
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

public class PartitionMemoryModelSyncHeapEncoding extends AbstractMemoryModel {

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static PartitionMemoryModelSyncHeapEncoding create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new PartitionMemoryModelSyncHeapEncoding(encoding);
  }

  private final Type addrType, valueType;
  private final ArrayType sizeArrType;
  private RecordType memType; // with multiple array types
  private TupleType stateType;
  
  private final HeapEncoding heapEncoding;
  
  private final Map<String, ArrayExpression> currentMemElems;
  private ArrayExpression currentSizeArr = null;
  
  private AliasAnalysis analyzer = null;
  private Expression prevDerefState = null;
  private ExpressionClosure currentState = null;
  
  private static final String MIX_TYPE_NAME = "mix";
  private static final String PTR_CONSTR_NAME = "ptr";
  private static final String SCALAR_CONSTR_NAME = "scalar";
  private static final String PTR_SELECTOR_NAME = "ptr-sel";
  private static final String SCALAR_SELECTOR_NAME = "scalar-sel";
  
  private final InductiveType mixType; // The list inductive data type
  private final Constructor ptrConstr, scalarConstr; // The constructors for cell type
  private final Selector ptrSel, scalarSel; // The selectors for cell type
  
  private final LoadingCache<Pair<GNode, String>, AliasVar> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<Pair<GNode, String>, AliasVar>(){
        public AliasVar load(Pair<GNode, String> key) {
          return getRepVar(key.fst());
        }
      });

  private PartitionMemoryModelSyncHeapEncoding(ExpressionEncoding encoding) {
    super(encoding);
    
    heapEncoding = SynchronousHeapEncoding.create(encoding);
    
    ExpressionManager exprManager = getExpressionManager();
    
    valueType = heapEncoding.getValueType();
    addrType = heapEncoding.getAddressType();
    
    memType = exprManager.recordType(
    		Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), 
    		Collections.<String>emptyList(), Collections.<Type>emptyList());
    
    sizeArrType = heapEncoding.getSizeArrType();
    
    stateType = exprManager.tupleType(
        Identifiers.uniquify(DEFAULT_STATE_TYPE), memType, sizeArrType);
    
    currentMemElems = Maps.newLinkedHashMap();
    
    
    scalarSel = exprManager.selector(SCALAR_SELECTOR_NAME, valueType);
    scalarConstr = exprManager.constructor(SCALAR_CONSTR_NAME, scalarSel);
    
    ptrSel = exprManager.selector(PTR_SELECTOR_NAME, addrType);
    ptrConstr = exprManager.constructor(PTR_CONSTR_NAME, ptrSel);

    mixType = exprManager.dataType(MIX_TYPE_NAME, scalarConstr, ptrConstr);
  }
  
/*  @Override
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
    
    Expression region = heapEncoding.freshRegion(regionName, regionNode);
    
     Update memory state 
    initCurrentMemElems(state.getChild(0));
    AliasVar regionRepVar = analyzer.getPointsToRepVar(ptr_var);
    
    {  Add newly sizeArrated region array to current memory elements 
      String regionArrName = getMemArrElemName(regionRepVar);
      if(!currentMemElems.containsKey(regionArrName)) {
        Type cellType = getArrayElemType(regionRepVar.getType());
        ArrayType arrType = exprManager.arrayType(addrType, cellType);
        ArrayExpression regionArr = exprManager.variable(regionArrName, arrType, false).asArray();
        currentMemElems.put(regionArrName, regionArr);
      }
    }
    
    {  Update the pointer array in current memory elements   
      String ptrRepArrName = getMemArrElemName(ptr_var);
      if(currentMemElems.containsKey(ptrRepArrName)) {
        ArrayExpression ptrRepArr = currentMemElems.get(ptrRepArrName);
        Type cellType = ptrRepArr.getType().getElementType();
        Expression locVarPrime = castExprToCell(region, cellType);
        ptrRepArr = ptrRepArr.update(ptr, locVarPrime);
        currentMemElems.put(ptrRepArrName, ptrRepArr);
      } else {
        xtc.type.Type ptrRepVarType = ptr_var.getType();
        CellKind ptrRepVarKind = CType.getCellKind(ptrRepVarType);
        
        Type cellType = CellKind.POINTER.equals(ptrRepVarKind) ? addrType : valueType;
        ArrayType arrType = exprManager.arrayType(addrType, cellType);
        ArrayExpression ptrRepArr = exprManager.variable(ptrRepArrName, arrType, false).asArray();
        assert(cellType.equals(region.getType()));
        ptrRepArr = ptrRepArr.update(ptr, region);
        currentMemElems.put(ptrRepArrName, ptrRepArr);
      }
    } 
    
    Type memPrimeType = getRecordTypeFromMap(
    		Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), currentMemElems);
    Expression memPrime = exprManager.record(memPrimeType, currentMemElems.values());
    
    Expression sizeArrPrime = heapEncoding.updateSizeArr(state.getChild(1).asArray(), region, size);    
    TupleExpression statePrime = getUpdatedState(state, memPrime, sizeArrPrime);
    setStateType(statePrime.getType());
    
    return statePrime;
  }*/
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));

    ExpressionManager exprManager = getExpressionManager();
    
    AliasVar ptr_var = loadRepVar(ptr.getNode());
    
    { /* Add newly allocated region array to current memory elements */
    	AliasVar regionRepVar = analyzer.getPointsToRepVar(ptr_var);
    	final String regionRepVarName = regionRepVar.getName();
    	final String regionRepScope = regionRepVar.getScope();
      Iterable<String> elemNames = state.getChild(0).asRecord().getType().getElementNames();
      boolean definedRegionVarRep = Iterables.any(elemNames, new Predicate<String>() {
      	@Override
      	public boolean apply(String elemName) {
      		return elemName.contains(regionRepVarName) 
      				&& elemName.contains(regionRepScope);
      	}
      });
      
      if(!definedRegionVarRep) {
        Type valueType = getArrayElemType(regionRepVar.getType());
        ArrayType arrType = exprManager.arrayType(addrType, valueType);
        String regionRepVarArrName = getMemArrElemName(regionRepVar);
        ArrayExpression regionArr = exprManager
        		.variable(regionRepVarArrName, arrType, false).asArray();
        currentMemElems.put(regionRepVarArrName, regionArr);
      }
    }
    
    /* Update memory state */

    AliasVar regionVar = analyzer.getAllocRegion(ptr_var);
    
    String regionName = regionVar.getName();
    GNode regionNode = GNode.create("PrimaryIdentifier", regionName);
    regionVar.getType().mark(regionNode);
    String regionScope = regionVar.getScope();
    regionNode.setProperty(CType.SCOPE, regionScope);
    
    Expression region = heapEncoding.freshRegion(regionName, regionNode);
    
    RecordExpression memory = updateMemoryState(state.getChild(0), ptr, region);
    ArrayExpression sizeArr = heapEncoding.updateSizeArr(state.getChild(1).asArray(), region, size);
    TupleExpression statePrime = getUpdatedState(state, memory, sizeArr);
    setStateType(statePrime.getType());
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));
    
    Expression sizeArr = heapEncoding.updateSizeArr(state.getChild(1).asArray(), ptr, size);
    TupleExpression statePrime = getUpdatedState(state, state.getChild(0), sizeArr);
    setStateType(statePrime.getType());
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));
    
    Expression sizeArr = heapEncoding.updateSizeArr(state.getChild(1).asArray(), ptr, size);    
    TupleExpression statePrime = getUpdatedState(state, state.getChild(0), sizeArr);
    setStateType(statePrime.getType());
    return statePrime;
  }
  
  @Override
  public TupleExpression free(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( addrType )); 
    
    Expression sizeZro = heapEncoding.getValueZero();
    Expression sizeArr = heapEncoding.updateSizeArr(state.getChild(1).asArray(), ptr, sizeZro);
    
    TupleExpression statePrime = getUpdatedState(state, state.getChild(0), sizeArr);
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
    	currentMemElems.putAll(getRecordElems(state.getChild(0)));
      prevDerefState = state;
    }
    
    ExpressionManager exprManager = getExpressionManager();
    
    Expression pValCell = null;
    AliasVar pRepVar = loadRepVar(p.getNode());
    
    String pArrName = getMemArrElemName(pRepVar);
    if(currentMemElems.containsKey(pArrName)) {
      ArrayExpression pArray = currentMemElems.get(pArrName);
      pValCell = pArray.index(p);
    } else { // Add an element to currentMemElem
      Type valueType = getArrayElemType(pRepVar.getType());
        
      ArrayType arrType = exprManager.arrayType(addrType, valueType);
      ArrayExpression pArray = exprManager.variable(pArrName, arrType, false).asArray();
      currentMemElems.put(pArrName, pArray);
      pValCell = pArray.index(p);
      
      String memTypePrime = Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE);
      Type currentMemType = getRecordTypeFromMap(memTypePrime, currentMemElems);
      Expression memPrime = exprManager.record(currentMemType, currentMemElems.values());
      Expression sizeArrPrime = updateSizeState(state.getChild(1));
      Expression statePrime = getUpdatedState(state, memPrime, sizeArrPrime);
      setCurrentState(state, statePrime);    
    }
    
    return castCellToExpr(pValCell, CType.getType(p.getNode()));
  }
  
  @Override
  public TupleExpression havoc(
      Expression state,
      Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( addrType ));
    Expression rval = getUnknownExpr(CType.getType(lval.getNode()));
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
    
    AliasVar ptrVar = loadRepVar(ptr.getNode());
    analyzer.heapAssign(ptrVar, CType.getType(ptr.getNode()));
    AliasVar regionVar = analyzer.getAllocRegion(ptrVar);
    
    String regionName = regionVar.getName();
    GNode regionNode = GNode.create("PrimaryIdentifier", regionName);
    regionVar.getType().mark(regionNode);
    regionNode.setProperty(CType.SCOPE, regionVar.getScope());
    
    Expression region = heapEncoding.freshRegion(regionName, regionNode);
    
    Expression currentMem = updateMemoryState(state.getChild(0), ptr, region);
    Expression currentSizeArr = updateSizeState(state.getChild(1), region, size);
    Expression statePrime = getUpdatedState(state, currentMem, currentSizeArr);
    setCurrentState(state, statePrime);
    
    return heapEncoding.validMalloc(currentSizeArr.asArray(), region, size);
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
  	return heapEncoding.disjointMemLayout();
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
    memType = stateType.asTuple().getElementTypes().get(0).asRecord();
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
          
          { /* Substitute the memory of expr */
            Expression memVar_mem = memoryVar.getChild(0);
            Expression memory_mem = memory.getChild(0);
            
            Map<String, ArrayExpression> memVarMemMap = getRecordElems(memVar_mem);
            Map<String, ArrayExpression> memoryMemMap = getRecordElems(memory_mem);
            
            List<Expression> oldArgs = Lists.newLinkedList();
            List<Expression> newArgs = Lists.newLinkedList();
            
            for(String name : memVarMemMap.keySet()) {
              if(memoryMemMap.containsKey(name)) {
              	oldArgs.add(memVarMemMap.get(name));
              	newArgs.add(memoryMemMap.get(name));
              }
            }
            
            if(!oldArgs.isEmpty()) {
              exprPrime = exprPrime.subst(oldArgs, newArgs);
              oldArgs.clear(); newArgs.clear();
            }
          }
          
          { /* Substitute the sizeArr of expr */
            Expression memVar_sizeArr = memoryVar.getChild(1);
            Expression memory_sizeArr = memory.getChild(1);
            
            exprPrime = exprPrime.subst(memVar_sizeArr, memory_sizeArr);
          }
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
          Expression memPrime = memory_mem;
          
          if(!memory_mem.getType().equals(expr_mem.getType())) {
          	
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
            memPrime = exprManager.record(expr_mem_type, elemMap.values());
          }
          
          /* Substitute the sizeArr of expr to sizeArrPrime */
          Expression expr_sizeArr = expr.getChild(1);
          Expression sizeArrPrime = null;
          
          if(expr_sizeArr.isVariable()) { // substitution makes no effect for variable
            assert(expr_sizeArr.equals(memoryVar.getChild(1)));
            sizeArrPrime = memory.getChild(1);
          } else {
            sizeArrPrime = expr_sizeArr.subst(memoryVar.getChild(0), memory_mem);
            sizeArrPrime = expr_sizeArr.subst(memoryVar.getChild(1), memory_sizeArr);
          }
          
          /* Update stateType -- static member of memory model */
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
    prevDerefState = null;
  }
  
  @Override
  public void setAliasAnalyzer(AliasAnalysis analyzer) {
    this.analyzer = analyzer;
    IOUtils.err().println(analyzer.displaySnapShort());
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
    return heapEncoding.validMalloc(state.getChild(1).asArray(), ptr, size);
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
    
  private RecordExpression updateMemoryState(Expression memState, Expression lval, Expression rval) {
    Map<String, ArrayExpression> transMap = getRecordElems(memState);
    Map<String, ArrayExpression> map = currentMemElems;
    boolean stateTypeChanged = !map.isEmpty();
    transMap.putAll(map);
    map = transMap;
	  
	  ExpressionManager exprManager = getExpressionManager();
	
	  AliasVar lvalRepVar = loadRepVar(lval.getNode());
	  String lvalRepArrName = getMemArrElemName(lvalRepVar);
	  
	  if(map.containsKey(lvalRepArrName)) {
	    ArrayExpression lvalRepArr = map.get(lvalRepArrName);
	    Type cellType = lvalRepArr.getType().getElementType();
	    rval = castExprToCell(rval, cellType);
	    lvalRepArr = lvalRepArr.update(lval, rval);
	    map.put(lvalRepArrName, lvalRepArr);
	  } else {
		  xtc.type.Type lvalRepType = lvalRepVar.getType();
	    Type cellType = getArrayElemType(lvalRepType);
	    ArrayType arrType = exprManager.arrayType(addrType, cellType);
	    ArrayExpression lvalArr = exprManager.variable(lvalRepArrName, arrType, false).asArray();
	    rval = castExprToCell(rval, cellType);
	    lvalArr = lvalArr.update(lval, rval);
	    map.put(lvalRepArrName, lvalArr);
	    stateTypeChanged = true;
	  }
	  
    Type recordTypePrime = memState.getType();
    
    if(stateTypeChanged) {
      String recordTypeName = Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE);
      recordTypePrime = getRecordTypeFromMap(recordTypeName, map);
    }
	  return exprManager.record(recordTypePrime, map.values());
	}
  
  private Expression updateSizeState(Expression sizeArrState) {
    if(currentSizeArr == null)
    	currentSizeArr = sizeArrState.asArray();
    return currentSizeArr;
  }
  
  private Expression updateSizeState(Expression sizeArrState, Expression lval, Expression rval) {
  	if(currentSizeArr == null)
  		currentSizeArr = sizeArrState.asArray();
    currentSizeArr = heapEncoding.updateSizeArr(currentSizeArr, lval, rval);
    return currentSizeArr;
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
  
  /**
   * Get the cell tyoe of the array in memory record for node with certain type
   * @param type
   */
  private Type getArrayElemType(xtc.type.Type type) {
    Type resType = null;
    switch(CType.getCellKind(type)) {
    case SCALAR :
    case BOOL :     resType = valueType; break;
    case ARRAY : {
      xtc.type.Type contentType = CType.unwrapped(type).toArray().getType();
      resType = getArrayElemType(contentType);
      break;
    }
    case POINTER :  resType = addrType; break;
    case STRUCTORUNION : {
      ElemType elemType = ElemType.getElemType(type);
      switch(elemType) {
      case SCALAR:  resType = valueType; break;
      case POINTER: resType = addrType; break;
      default:      resType = mixType; 
      }
      break;
    }
    default:    throw new IllegalArgumentException("Unsupported type " + type);
    }
    return resType;
  }
  
  private void setCurrentState(Expression state, Expression statePrime) {
    currentState = suspend(state, statePrime);
  }

	private enum ElemType {
	  SCALAR,
	  POINTER,
	  MIX;

	  static ElemType getElemType(xtc.type.Type type) {
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
		  assert !(pointer && scalar);
		  if(pointer)         return  ElemType.POINTER;
		  else if(scalar)     return  ElemType.SCALAR;
		  else                return  ElemType.MIX;
		}
	}
	
	private Expression getUnknownExpr(xtc.type.Type type) {
    CellKind kind = CType.getCellKind(type);
    switch(kind) {
    case POINTER: 
    	return heapEncoding.getUnknownAddress();
    case SCALAR:  
    	return heapEncoding.getUnknownValue();
    case BOOL:
    	return heapEncoding.getUnknownValue();
    default: throw new IllegalArgumentException("Invalid kind " + kind);
    }
	}
	
	private Expression castCellToExpr(Expression pValCell, xtc.type.Type pType) {
		ExpressionManager exprManager = getExpressionManager();
		Expression resVal = pValCell;
	  if(mixType.equals(pValCell.getType())) {
	    CellKind kind = CType.getCellKind(CType.unwrapped(pType));
	    switch(kind) {
	    case SCALAR:
	    case BOOL:
	    	resVal = exprManager.select(scalarSel, pValCell); break;
	    case POINTER:
	    	resVal = exprManager.select(ptrSel, pValCell); break;
	    default:
	      throw new IllegalArgumentException("Invalid kind " + kind);
	    }
	  }
	  return resVal;
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
}
