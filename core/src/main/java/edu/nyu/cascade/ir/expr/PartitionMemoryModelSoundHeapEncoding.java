package edu.nyu.cascade.ir.expr;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Iterator;
import java.util.Set;
import java.util.concurrent.ExecutionException;

import xtc.tree.GNode;
import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableMap;
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
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.ArrayType;
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

public class PartitionMemoryModelSoundHeapEncoding extends AbstractMemoryModel {

  /** Create an expression factory with the given pointer and word sizes. A pointer must be an 
   * integral number of words.
   */
  public static PartitionMemoryModelSoundHeapEncoding create(
      ExpressionEncoding encoding)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new PartitionMemoryModelSoundHeapEncoding(encoding);
  }
  
  private final Type addrType, valueType;
  private RecordType memType, sizeArrType; // with multiple array types
  private TupleType stateType;
  
  private final HeapEncoding heapEncoding;
  
  private final Map<String, ArrayExpression> currentMemElems, currentSizeElems;
  
  private AliasAnalysis analyzer = null;
  private Expression prevDerefState = null;
  private ExpressionClosure currentState = null;
  
  private final LoadingCache<Pair<GNode, String>, AliasVar> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<Pair<GNode, String>, AliasVar>(){
        public AliasVar load(Pair<GNode, String> key) {
          return getRepVar(key.fst());
        }
      });
  
  private PartitionMemoryModelSoundHeapEncoding(ExpressionEncoding encoding) {
    super(encoding);
    
    heapEncoding = LinearHeapSoundEncoding.create(encoding);
    
    ExpressionManager exprManager = getExpressionManager();
    
    valueType = heapEncoding.getValueType();
    addrType = heapEncoding.getAddressType();
    
    memType = exprManager.recordType(
    		Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), 
        Collections.<String>emptyList(), Collections.<Type>emptyList());
    
    sizeArrType = exprManager.recordType(
        Identifiers.uniquify(DEFAULT_ALLOC_STATE_TYPE), 
        Collections.<String>emptyList(), Collections.<Type>emptyList());
    
    stateType = exprManager.tupleType(
        Identifiers.uniquify(DEFAULT_STATE_TYPE), memType, sizeArrType);
    
    currentMemElems = Maps.newLinkedHashMap();
    currentSizeElems = Maps.newLinkedHashMap();
  }
  
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
    RecordExpression sizeArr = updateSizeState(state.getChild(1), region, size);
    TupleExpression statePrime = getUpdatedState(state, memory, sizeArr);
    setStateType(statePrime.getType());
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));
    
    RecordExpression sizeArr = updateSizeState(state.getChild(1), ptr, size);
    TupleExpression statePrime = getUpdatedState(state, state.getChild(0), sizeArr);
    setStateType(statePrime.getType());
    return statePrime;
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));
    
    RecordExpression sizeArr = updateSizeState(state.getChild(1), ptr, size);
    TupleExpression statePrime = getUpdatedState(state, state.getChild(0), sizeArr);
    setStateType(statePrime.getType());
    return statePrime;
  }
  
  @Override
  public TupleExpression free(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( addrType )); 
    
    Expression sizeZro = heapEncoding.getValueZero();
    Expression sizeArr = updateSizeState(state.getChild(1), ptr, sizeZro);
    
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
    
    return pValCell;
  }
  
  @Override
  public TupleExpression havoc(
      Expression state,
      Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( addrType ));
    Expression rval = heapEncoding.getUnknownValue();
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
    
    /* Find related heap regions and alloc array */
    Iterable<AliasVar> equivAliasVars = analyzer.getEquivClass(regionVar);
    Iterable<Iterable<Expression>> varSets = 
    		heapEncoding.getCategorizedVars(equivAliasVars);
    
    String sizeArrName = getSizeArrElemName(regionVar);
    assert currentSizeElems.containsKey(sizeArrName);
    ArrayExpression sizeArr = currentSizeElems.get(sizeArrName);
    
    return heapEncoding.validMalloc(Iterables.get(varSets, 2), sizeArr, region, size);
  }
  
  @Override
  public Expression addressOf(Expression content) {
    CellKind kind = CType.getCellKind(CType.getType(content.getNode()));
    switch(kind) {
    case STRUCTORUNION: 
    case ARRAY:   return content;
    default:      return content.getChild(1);
    }
  }
  
  @Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
  	
  	Map<String, ArrayExpression> memMap = getRecordElems(state.getChild(0));
    Map<String, ArrayExpression> sizeMap = getRecordElems(state.getChild(1));
    
    ImmutableMap<AliasVar, Set<AliasVar>> map = analyzer.snapshot();
    
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    
    for(AliasVar repVar : map.keySet()) {
    	String repVarMemArrName = getMemArrElemName(repVar);
      
      /* If the repVar is referred in the execution paths */
      if(!memMap.containsKey(repVarMemArrName)) continue;
      
      /* Categorize vars into stVar, stReg, and hpReg */
      Iterable<AliasVar> equivAliasVars = analyzer.getEquivClass(repVar);
      Iterable<Iterable<Expression>> varSets = 
      		heapEncoding.getCategorizedVars(equivAliasVars);
      
      String sizeArrName = getSizeArrElemName(repVar);
      ArrayExpression sizeArr = sizeMap.get(sizeArrName); // might be null
      builder.addAll(heapEncoding.disjointMemLayout(varSets, sizeArr));
    }
    
    return builder.build();
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
  public RecordType getAllocType() {
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
    sizeArrType = stateType.asTuple().getElementTypes().get(1).asRecord();
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
            
            Map<String, ArrayExpression> memVarSizeArrMap = getRecordElems(memVar_sizeArr);
            Map<String, ArrayExpression> memorySizeArrMap = getRecordElems(memory_sizeArr);
            
            List<Expression> oldArgs = Lists.newLinkedList();
            List<Expression> newArgs = Lists.newLinkedList();
            
            for(String name : memVarSizeArrMap.keySet()) {
              if(memorySizeArrMap.containsKey(name)) {
              	oldArgs.add(memVarSizeArrMap.get(name));
              	newArgs.add(memorySizeArrMap.get(name));
              }
            }
            
            if(!oldArgs.isEmpty()) {
              exprPrime = exprPrime.subst(oldArgs, newArgs);
              oldArgs.clear(); newArgs.clear();
            }
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
          
          if(!memory_mem.getType().equals(expr_mem.getType())){
          	
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

          /* Substitute the sizeArr of expr to memPrime */
          Expression expr_sizeArr = expr.getChild(1);
          Expression sizeArrPrime = memory_sizeArr;
                   
          if(!memory_sizeArr.getType().equals(expr_sizeArr.getType())){

          	RecordType expr_sizeArr_type = expr_sizeArr.getType().asRecord();
          
            /* Initialize elemMap from the expr_mem */
            Map<String, Expression> elemMap = Maps.newLinkedHashMap();
          
            Iterator<String> nameItr = expr_sizeArr_type.getElementNames().iterator();
            Iterator<? extends Expression> elemItr = expr_sizeArr.getChildren().iterator();
            while(nameItr.hasNext() && elemItr.hasNext()) {
              String name = nameItr.next();
              Expression elem = elemItr.next();
              elem = elem.subst(memoryVar.getChild(0), memory_mem);
              elem = elem.subst(memoryVar.getChild(1), memory_sizeArr);
              elemMap.put(name, elem);
            }
          
            sizeArrPrime = exprManager.record(expr_sizeArr_type, elemMap.values());
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
    currentSizeElems.clear();
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
	  
	  /* Find related heap regions and alloc array */
	  AliasVar pRepVar = loadRepVar(ptr.getNode());
	  AliasVar ptr2RepVar = analyzer.getPointsToRepVar(pRepVar);
	  Iterable<AliasVar> equivAliasVars = analyzer.getEquivClass(ptr2RepVar);
	    
	  Iterable<Iterable<Expression>> varSets = 
	  		heapEncoding.getCategorizedVars(equivAliasVars);
	  
	  /* Get the related alloc array */
    Map<String, ArrayExpression> map = getRecordElems(state.getChild(1));
    String sizeArrName = getSizeArrElemName(ptr2RepVar);
    ArrayExpression sizeArr = map.get(sizeArrName);
    assert sizeArr != null;
	    
	  Collection<BooleanExpression> res = heapEncoding.validMemAccess(varSets, sizeArr, ptr);
	  
	  return getExpressionManager().or(res);
	}

	@Override
	public BooleanExpression valid(Expression state, Expression ptr, Expression size) {
	  Preconditions.checkArgument(ptr.getType().equals( addrType ));
	  Preconditions.checkArgument(size.getType().equals( valueType ));
	  
	  /* Find related heap regions and alloc array */
	  AliasVar pRepVar = loadRepVar(ptr.getNode());
	  AliasVar ptr2RepVar = analyzer.getPointsToRepVar(pRepVar);
	  Iterable<AliasVar> equivAliasVars = analyzer.getEquivClass(ptr2RepVar);
	  Iterable<Iterable<Expression>> varSets = 
	  		heapEncoding.getCategorizedVars(equivAliasVars);
	    
	  /* Get the related alloc array */
    Map<String, ArrayExpression> map = getRecordElems(state.getChild(1));
    String sizeArrName = getSizeArrElemName(ptr2RepVar);
    ArrayExpression sizeArr = map.get(sizeArrName);
    assert sizeArr != null;
	  
	  Collection<BooleanExpression> res = heapEncoding.validMemAccess(varSets, sizeArr, ptr, size);
	  
	  return getExpressionManager().or(res);
	}

	@Override
	public BooleanExpression valid_malloc(Expression state, Expression ptr, Expression size) {

    /* Find related heap regions and alloc array */
    AliasVar pRepVar = loadRepVar(ptr.getNode());
    pRepVar = analyzer.getPointsToRepVar(pRepVar);
    
    Iterable<AliasVar> equivAliasVars = analyzer.getEquivClass(pRepVar);
    Iterable<Iterable<Expression>> varSets = heapEncoding.getCategorizedVars(equivAliasVars);
    
    Map<String, ArrayExpression> map = getRecordElems(state.getChild(1));
    String sizeArrName = getSizeArrElemName(pRepVar);
    ArrayExpression sizeArr = map.get(sizeArrName);
    assert sizeArr != null;
    
    return heapEncoding.validMalloc(Iterables.get(varSets, 2), sizeArr, ptr, size);
	}

	@Override
	public BooleanExpression valid_free(Expression state, Expression ptr) {
	  /* Find related heap regions and alloc array */
	  AliasVar pRepVar = loadRepVar(ptr.getNode());
	  AliasVar ptr2RepVar = analyzer.getPointsToRepVar(pRepVar);
	  
	  Map<String, ArrayExpression> map = getRecordElems(state.getChild(1));
    String sizeArrName = getSizeArrElemName(ptr2RepVar);
    ArrayExpression sizeArr = map.get(sizeArrName);
    assert sizeArr != null;
	  return heapEncoding.validFree(sizeArr, ptr);
	}
  
  @Override
  public Expression substAlloc(Expression expr) {
    return expr;
  }
  
  private RecordExpression updateMemoryState(Expression memState, Expression lval, Expression rval) {
    return updateRecord(memState.asRecord(), lval, rval, true);
  }
  
  private RecordExpression updateSizeState(Expression sizeArrState, Expression lval, Expression rval) {
    return updateRecord(sizeArrState.asRecord(), lval, rval, false);
  }
  
  private RecordExpression updateSizeState(Expression sizeArrState) {
  	Preconditions.checkArgument(sizeArrState.isRecord());
    Map<String, ArrayExpression> map = getRecordElems(sizeArrState);
    int preSize = map.size();
    map.putAll(currentSizeElems);
    
    if(map.size() > preSize) { // type changed
    	String recordTypeName = Identifiers.uniquify(DEFAULT_ALLOC_STATE_TYPE);
    	RecordType recordPrimeType = getRecordTypeFromMap(recordTypeName, map);
    	return getExpressionManager().record(recordPrimeType, map.values());
    } else {
    	if(!map.isEmpty()) // content changed
    		return getExpressionManager().record(sizeArrState.getType(), map.values());
    	else
    		return sizeArrState.asRecord();
    }    
  }
  
  private RecordExpression updateRecord(RecordExpression record, Expression lval, Expression rval, boolean mem) {
    Map<String, ArrayExpression> transMap = getRecordElems(record);
    Map<String, ArrayExpression> map = mem ? currentMemElems : currentSizeElems;
    boolean stateTypeChanged = !map.isEmpty();
    transMap.putAll(map);
    map = transMap;
    
    ExpressionManager exprManager = getExpressionManager();

    AliasVar lvalRepVar = loadRepVar(lval.getNode());    
    String lvalRepArrName = mem ? getMemArrElemName(lvalRepVar) : getSizeArrElemName(lvalRepVar);
    
    if(map.containsKey(lvalRepArrName)) {
      ArrayExpression lvalRepArr = map.get(lvalRepArrName);
//      Type valueType = lvalRepArr.getType().getElementType();
//      rval = castExprToCell(rval, valueType);
      lvalRepArr = lvalRepArr.update(lval, rval);
      map.put(lvalRepArrName, lvalRepArr);
    } else {
      xtc.type.Type lvalRepType = lvalRepVar.getType();
      Type valueType = getArrayElemType(lvalRepType);
      ArrayType arrType = exprManager.arrayType(addrType, valueType);
      ArrayExpression lvalArr = exprManager.variable(lvalRepArrName, arrType, false).asArray();
//      rval = castExprToCell(rval, valueType);
      lvalArr = lvalArr.update(lval, rval);
      map.put(lvalRepArrName, lvalArr);
      stateTypeChanged = true;
    }
    
    Type recordTypePrime = record.getType();
    
    if(stateTypeChanged) {
      String recordTypeName = mem ? Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE) :
      	Identifiers.uniquify(DEFAULT_ALLOC_STATE_TYPE);
      recordTypePrime = getRecordTypeFromMap(recordTypeName, map);
    }
    return exprManager.record(recordTypePrime, map.values());
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
   * Get the cell type of the array in memory record for node with certain type
   * @param type
   */
  private Type getArrayElemType(xtc.type.Type type) {
    Type resType = null;
    switch(CType.getCellKind(type)) {
    case SCALAR :
    case BOOL :     resType = valueType; break;
    case ARRAY : 
    case POINTER :  
    case STRUCTORUNION : resType = addrType; break;
    default:    throw new IllegalArgumentException("Unsupported type " + type);
    }
    return resType;
  }
  
  private void setCurrentState(Expression state, Expression statePrime) {
    Expression stateTmp = statePrime;
    if(currentState != null)    stateTmp = currentState.eval(statePrime);
    currentState = suspend(state, stateTmp);
  }
}
