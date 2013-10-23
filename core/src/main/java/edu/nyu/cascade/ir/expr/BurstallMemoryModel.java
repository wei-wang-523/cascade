package edu.nyu.cascade.ir.expr;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.type.FieldReference;
import xtc.type.Reference;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.IREquivClosure;
import edu.nyu.cascade.c.preprocessor.IRPreProcessor;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.c.preprocessor.typeanalysis.TypeAnalyzer;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;

/**
 * Burstall memory model, multiple memory arrays for various type.
 * These arrays types map pointer type to either pointer type or 
 * scalar type. 
 * 
 * The state of memory is a record with multiple arrays for various 
 * types. 
 * 
 * 
 * @author Wei
 *
 */
public class BurstallMemoryModel extends AbstractMemoryModel {

  public static BurstallMemoryModel create(
      ExpressionEncoding encoding, IRPartitionHeapEncoder heapEncoder)
      throws ExpressionFactoryException {
    Preconditions.checkArgument(encoding instanceof PointerExpressionEncoding);
    return new BurstallMemoryModel(encoding, heapEncoder);
  }

  private final Type addrType, valueType;
  private RecordType memType, sizeArrType;
  private TupleType stateType;
  
  private final IRPartitionHeapEncoder heapEncoder;
  
  private final Map<String, ArrayExpression> sideEffectMem;
  private final Map<String, ExpressionClosure> sideEffectMemClosure;
  private final Map<String, ExpressionClosure> sideEffectSizeClosure;
  
  private TypeAnalyzer analyzer = null;

    private BurstallMemoryModel(ExpressionEncoding encoding,
				IRPartitionHeapEncoder heapEncoder) {
    super(encoding);
    
    this.heapEncoder = heapEncoder;    
    valueType = heapEncoder.getValueType();
    addrType = heapEncoder.getAddressType();
    
    ExpressionManager exprManager = getExpressionManager();
    
    memType = exprManager.recordType(
    		Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE), 
        Collections.<String>emptyList(), Collections.<Type>emptyList());
    
    sizeArrType = exprManager.recordType(
        Identifiers.uniquify(DEFAULT_ALLOC_STATE_TYPE), 
        Collections.<String>emptyList(), Collections.<Type>emptyList());
    
    stateType = exprManager.tupleType(
        Identifiers.uniquify(DEFAULT_STATE_TYPE), memType, sizeArrType);
    
    sideEffectMem = Maps.newLinkedHashMap();
    sideEffectMemClosure = Maps.newLinkedHashMap();
    sideEffectSizeClosure = Maps.newLinkedHashMap();
  }
  
  @Override
  public TupleExpression alloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType )); 
    
    IRVar regionVar = analyzer.getAllocateElem(ptr.getNode());
    
    String regionName = regionVar.getName();
    GNode regionNode = GNode.create("PrimaryIdentifier", regionName);
    regionVar.getType().mark(regionNode);
    String regionScope = regionVar.getScope().getQualifiedName();
    regionNode.setProperty(CType.SCOPE, regionScope);
    
    Expression region = heapEncoder.freshRegion(regionName, regionNode);
    
    RecordExpression memory = updateMemoryState(state.getChild(0), ptr, region);
    RecordExpression sizeArr = updateSizeState(state.getChild(1), region, size);
    return getUpdatedState(state, memory, sizeArr);
  }
  
  @Override 
  public TupleExpression declareArray(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));

    RecordExpression sizeArr = updateSizeState(state.getChild(1), ptr, size);
    return getUpdatedState(state, state.getChild(0), sizeArr);
  }
  
  @Override 
  public TupleExpression declareStruct(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));

    RecordExpression sizeArr = updateSizeState(state.getChild(1), ptr, size);
    return getUpdatedState(state, state.getChild(0), sizeArr);
  }

  @Override
	public TupleExpression free(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( addrType )); 
    
    Expression sizeZro = heapEncoder.getValueZero();
    Expression sizeArr = updateSizeState(state.getChild(1), ptr, sizeZro);
    
    return getUpdatedState(state, state.getChild(0), sizeArr);
	}

	@Override
	public TupleExpression assign(
	    Expression state,
	    Expression lval,
	    Expression rval) {
    Preconditions.checkArgument(lval.getType().equals( addrType ));
    Preconditions.checkArgument(rval.getType().equals( valueType )
    		|| rval.getType().equals( addrType ));
    
    RecordExpression memory = updateMemoryState(state.getChild(0), lval, rval);
    return getUpdatedState(state, memory, state.getChild(1));
	}

	@Override
	public Expression deref(Expression state, Expression p) {
    Preconditions.checkArgument(addrType.equals(p.getType()));
    xtc.type.Type pType = analyzer.getRep(p.getNode());
    String pTypeName = analyzer.getRepName(pType);
    updateMemArray(state, pType, pTypeName);
    ArrayExpression pArray = getMemArray(state, pTypeName);    
    return heapEncoder.indexMemArr(pArray, p);
	}

	@Override
	public TupleExpression havoc(
	    Expression state,
	    Expression lval) {
    Preconditions.checkArgument(lval.getType().equals( addrType ));
    
    Expression rval = heapEncoder.getUnknownValue(CType.getType(lval.getNode()));
    RecordExpression memory = updateMemoryState(state.getChild(0), lval, rval);
    return getUpdatedState(state, memory, state.getChild(1));
	}

	@Override
	public Expression createLval(Expression state, String name,
	    IRVarInfo info, Node node) {	
		xtc.type.Type type = CType.getType(node);
		return heapEncoder.freshAddress(name, info, CType.unwrapped(type));
	}

	@Override
	public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));
    
    IRVar regionVar = analyzer.getAllocateElem(ptr.getNode());
    xtc.type.Type regionType = regionVar.getType();
    
    String regionName = regionVar.getName();
    GNode regionNode = GNode.create("PrimaryIdentifier", regionName);
    regionType.mark(regionNode);
    regionNode.setProperty(CType.SCOPE, regionVar.getScope().getQualifiedName());
    
    Expression region = heapEncoder.freshRegion(regionName, regionNode);

    /* Update side effect memory state */
    xtc.type.Type pType = analyzer.getRep(ptr.getNode());
    String pTypeName = analyzer.getRepName(pType);
    ArrayExpression array1 = popMemArray(state, pType, pTypeName);
    array1 = heapEncoder.updateMemArr(array1, ptr, region);
    String ptrArrName = getMemArrElemName(pTypeName);
    updateSideEffectMemClosure(ptrArrName, suspend(state, array1));
    
    String regionTypeName = analyzer.getRepName(regionType);
    updateMemArray(state, regionType, regionTypeName);
    
    /* Update side effect size state */
    ArrayExpression array2 = popSizeArray(state, regionType, regionTypeName);
    array2 = heapEncoder.updateSizeArr(array2, region, size);
    String regArrName = getSizeArrElemName(regionTypeName);
    updateSideEffectSizeClosure(regArrName, suspend(state, array2));
    
    /* Find related heap regions and size array */
    IREquivClosure equivAliasVars = analyzer.getEquivClass(regionType);    
    return heapEncoder.validMalloc(equivAliasVars, array2, region, size);
	}

	@Override
	public Expression addressOf(Expression content) {
  	return heapEncoder.addressOf(content);
	}

	@Override
	public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {    
    ImmutableMap<xtc.type.Type, Set<IRVar>> map = analyzer.snapshot();
    
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    
    Set<String> memMapKeySet = getRecordElems(state.getChild(0)).keySet();
    Map<String, ArrayExpression> sizeMap = getRecordElems(state.getChild(1));
    
    for(xtc.type.Type type : map.keySet()) {
    	String typeName = analyzer.getRepName(type);
    	String memArrName = getMemArrElemName(typeName);
    	
    	/* If the repVar is not referred in the execution paths.
    	 * Special case: memMapKeySet contains $STRUCT.FOO, the type name
    	 * is $STRUCT. We should keep it.
    	 */
    	boolean isStructOrUnion = type.resolve().isStruct() || type.resolve().isUnion();
    	if(!isStructOrUnion && 
    			!memMapKeySet.contains(memArrName)) continue;
    	
    	/* Categorize vars into stVar, stReg, and hpReg */
    	IREquivClosure equivAliasVars = analyzer.getEquivClass(type);    	
      String sizeArrName = getSizeArrElemName(typeName);
      ArrayExpression sizeArr = sizeMap.get(sizeArrName); // might be null
      builder.addAll(heapEncoder.disjointMemLayout(equivAliasVars, sizeArr));
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
	public TupleType getStateType() {
	  return stateType;
	}

  @Override
  public boolean setStateType(Type stateType) {
  	Preconditions.checkArgument(stateType.isTuple() && stateType.asTuple().size() == 2);
  	
  	if(this.stateType.equals(stateType))	return false;
  	
    this.stateType = stateType.asTuple();
    memType = stateType.asTuple().getElementTypes().get(0).asRecord();
    sizeArrType = stateType.asTuple().getElementTypes().get(1).asRecord();
    return true;
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
    Preconditions.checkArgument(stateType.equals(memoryVar.getType()));
    return new ExpressionClosure() {
      @Override
      public Expression eval(final Expression memory) {
//        Preconditions.checkArgument(memory.getType().equals(memoryVar.getType()));
        Preconditions.checkArgument(!isState(expr));
        
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
  
  public boolean hasSideEffect() {
    return !(sideEffectMem.isEmpty() && sideEffectMemClosure.isEmpty()
    		&& sideEffectSizeClosure.isEmpty());
  }
  
  public Expression clearSideEffect(Expression state) {
  	Preconditions.checkArgument(state.isTuple());
  	Expression mem = state.getChild(0);
  	Expression size = state.getChild(1);
  	
  	Expression memPrime = mem;
  	
  	{	/* Update memory */
  		Map<String, ArrayExpression> map = Maps.newLinkedHashMap();
  		if(!sideEffectMemClosure.isEmpty()) {
  			for(Entry<String, ExpressionClosure> entry 
  					: sideEffectMemClosure.entrySet()) {
  				Expression expr = entry.getValue().eval(state);
  				map.put(entry.getKey(), expr.asArray());
  			}
  			sideEffectMemClosure.clear();
  		}
  	
  		if(!sideEffectMem.isEmpty()) {
  			map.putAll(sideEffectMem);
  			sideEffectMem.clear();
  		}
  		
  		if(!map.isEmpty()) memPrime = clearSideEffectMem(mem, map);
  	}
  	
  	Expression sizePrime = size;
  	
  	{ /* Update size */
  		Map<String, ArrayExpression> map = Maps.newLinkedHashMap();
  		if(!sideEffectSizeClosure.isEmpty()) {
  			for(Entry<String, ExpressionClosure> entry 
  					: sideEffectSizeClosure.entrySet()) {
  				Expression expr = entry.getValue().eval(state);
  				map.put(entry.getKey(), expr.asArray());
  			}
  			sideEffectSizeClosure.clear();
  		}
  	
  		if(!map.isEmpty()) sizePrime = clearSideEffectSize(size, map);
  	}
  	
    return getUpdatedState(state, memPrime, sizePrime);
  }
  
  @Override
  public void setPreProcessor(IRPreProcessor<?> analyzer) {
  	Preconditions.checkArgument(analyzer instanceof TypeAnalyzer);
    this.analyzer = (TypeAnalyzer) analyzer;
    IOUtils.debug().pln(analyzer.displaySnapShot());
  }

  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    
    /* Find related heap regions and size array */
    xtc.type.Type ptr2Type = analyzer.getPointsToElem(ptr.getNode());
    IREquivClosure equivAliasVars = analyzer.getEquivClass(ptr2Type);
    
    if(equivAliasVars.getElements() == null) {
    	IOUtils.err().println("No variables in type " + ptr2Type.getName());
    	return getExpressionManager().ff();
    }
    
    /* Get the related alloc array */
    String ptr2TypeName = analyzer.getRepName(ptr2Type);
    ArrayExpression sizeArr = popSizeArray(state, ptr2Type, ptr2TypeName);
      
    Collection<BooleanExpression> res = heapEncoder.validMemAccess(equivAliasVars, sizeArr, ptr);
    
    return getExpressionManager().or(res);
  }
  
  @Override
  public BooleanExpression valid(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));

    /* Find related heap regions and size array */
    xtc.type.Type ptr2Type = analyzer.getPointsToElem(ptr.getNode());
    IREquivClosure equivAliasVars = analyzer.getEquivClass(ptr2Type);
    
    if(equivAliasVars == null) {
    	IOUtils.err().println("No variables in type " + ptr2Type.getName());
    	return getExpressionManager().ff();
    }
    
    /* Get the related alloc array */
    String ptr2TypeName = analyzer.getRepName(ptr2Type);
    ArrayExpression sizeArr = popSizeArray(state, ptr2Type, ptr2TypeName);

    Collection<BooleanExpression> res = heapEncoder.validMemAccess(equivAliasVars, sizeArr, ptr, size);
    
    return getExpressionManager().or(res);
  }
  
  @Override
  public BooleanExpression valid_malloc(Expression state, Expression ptr, Expression size) {
    Preconditions.checkArgument(ptr.getType().equals( addrType ));
    Preconditions.checkArgument(size.getType().equals( valueType ));
    
    /* Find related heap regions and alloc array */
    xtc.type.Type ptr2Type = analyzer.getPointsToElem(ptr.getNode());   
    IREquivClosure equivAliasVars = analyzer.getEquivClass(ptr2Type);
    
    Map<String, ArrayExpression> map = getRecordElems(state.getChild(1));
    String typeName = analyzer.getRepName(ptr2Type);
    String sizeArrName = getSizeArrElemName(typeName);
    ArrayExpression sizeArr = map.get(sizeArrName);
    assert sizeArr != null;
    
    BooleanExpression res = heapEncoder.validMalloc(equivAliasVars, sizeArr, ptr, size);
    return res;
  }
  
  @Override
  public BooleanExpression valid_free(Expression state, Expression ptr) {
  	Preconditions.checkArgument(ptr.getType().equals( addrType ));
  	
    /* Find related heap regions and alloc array */
    xtc.type.Type ptr2Type = analyzer.getPointsToElem(ptr.getNode());
    String ptr2TypeName = analyzer.getRepName(ptr2Type);
    ArrayExpression sizeArr = popSizeArray(state, ptr2Type, ptr2TypeName);

    return heapEncoder.validFree(sizeArr, ptr);
  }
  
  @Override
  public Expression substSizeArr(Expression expr) {
    return expr;
  }
  
  /**
	 * Update memory state with side effect map
	 * @param record
	 * @param sideEffectMap
	 * @return updated memory state
	 */
	private RecordExpression clearSideEffectMem(Expression record,
			Map<String, ArrayExpression> sideEffectMap) {
		Preconditions.checkArgument(record.isRecord());
		if(sideEffectMap.isEmpty())	return record.asRecord();
		RecordExpression res = clearSideEffectRecord(record.asRecord(), sideEffectMap, true);
		sideEffectMap.clear();
		return res;
	}

	/**
	 * Update size state with side effect map
	 * @param record
	 * @param sideEffectMap
	 * @return updated size state
	 */
	private RecordExpression clearSideEffectSize(Expression record,
			Map<String, ArrayExpression> sideEffectMap) {
		Preconditions.checkArgument(record.isRecord());
		if(sideEffectMap.isEmpty())	return record.asRecord();
		RecordExpression res = clearSideEffectRecord(record.asRecord(), sideEffectMap, false);
		sideEffectMap.clear();
		return res;
	}

	/**
	 * Update <code>record</code> with side effect map
	 * @param record
	 * @param sideEffectMap
	 * @param mem is true indicate is memory update, otherwise is size update
	 * @return updated record
	 */
	private RecordExpression clearSideEffectRecord(RecordExpression record, 
			Map<String, ArrayExpression> sideEffectMap, boolean mem) {
		Preconditions.checkArgument(!sideEffectMap.isEmpty());
	  
	  Map<String, ArrayExpression> map = getRecordElems(record);
	  map.putAll(sideEffectMap);
	  
	  Type recordTypePrime = record.getType();
	  if(map.size() > record.getArity()) {
	  	String recordTypeName = mem ? Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE) :
	  		Identifiers.uniquify(DEFAULT_ALLOC_STATE_TYPE);
	  	recordTypePrime = getRecordTypeFromMap(recordTypeName, map);
	  } 
	  return getExpressionManager().record(recordTypePrime, map.values());
	}

	/**
   * Update memory state with assignment lval := rval
   * @param record
   * @param lval
   * @param rval
   * @return updated memory state
   */
  private RecordExpression updateMemoryState(Expression record, Expression lval, Expression rval) {
  	Preconditions.checkArgument(record.isRecord());
  	RecordExpression res = updateRecord(record.asRecord(), lval, rval, true);
  	return res; 	
  }
  
  /**
   * Update size state with assignment lval := rval
   * @param record
   * @param lval
   * @param rval
   * @return updated size state
   */
  private RecordExpression updateSizeState(Expression record, Expression lval, Expression rval) {
  	Preconditions.checkArgument(record.isRecord());
  	RecordExpression res = updateRecord(record.asRecord(), lval, rval, false);
  	return res;
  }
  
  /**
   * Update <code>record</code> with assignment lval := rval
   * @param record
   * @param lval
   * @param rval
   * @param mem is true indicate is memory update, otherwise is size update
   * @return updated record
   */
  private RecordExpression updateRecord(RecordExpression record, Expression lval, Expression rval, boolean mem) {
    Map<String, ArrayExpression> map = getRecordElems(record);
    ExpressionManager exprManager = getExpressionManager();
    int preSize = map.size();
    
    if(mem) {
    	xtc.type.Type lType = analyzer.getRep(lval.getNode());
    	String lTypeName = analyzer.getRepName(lType);    	
    	assert !lTypeName.equals(Identifiers.CONSTANT);
    	
    	/* Update the memory array for lval type in memory */
    	ArrayExpression lMemArr = null;
    	String lMemArrName = getMemArrElemName(lTypeName);
    	if(!map.containsKey(lMemArrName)) {
    		Type valueType = heapEncoder.getArrayElemType(lType);
    		lMemArr = exprManager.arrayVar(lMemArrName, addrType, valueType, false);
    	} else {
    		lMemArr = map.get(lMemArrName);
    	}
    	
    	lMemArr = heapEncoder.updateMemArr(lMemArr, lval, rval);
      map.put(lMemArrName, lMemArr);
      
      /* Update the mem array for rval type in memory */
    	if(rval.getNode() != null) {
    		xtc.type.Type rType = analyzer.getRep(rval.getNode());
    		String rTypeName = analyzer.getRepName(rType);
        if(!rTypeName.equals(Identifiers.CONSTANT)) {
        	String rMemArrName = getMemArrElemName(rTypeName);
        	if(!map.containsKey(rMemArrName)) {
        		Type valueType = heapEncoder.getArrayElemType(rType);
        		ArrayExpression rMemArr = getExpressionManager()
        				.arrayVar(rMemArrName, addrType, valueType, false);
        		map.put(rMemArrName, rMemArr);
        	}
        }
    	}
    	
    	Type recordType = record.getType();
    	if(map.size() > preSize) {
    		String typeName = Identifiers.uniquify(DEFAULT_MEMORY_STATE_TYPE);
    		recordType = getRecordTypeFromMap(typeName, map);
    	}
    	
    	return exprManager.record(recordType, map.values());
    } else {
    	Type recordType = record.getType();    	
    	ArrayExpression lvalRepArr = null;
    	xtc.type.Type lType = analyzer.getRep(lval.getNode());
    	String lTypeName = analyzer.getRepName(lType);
     	String lSizeArrName = getSizeArrElemName(lTypeName);
     	if(!map.containsKey(lSizeArrName)) {
     		/* Initialize as constant array with zero everywhere */
     		lvalRepArr = heapEncoder.getConstSizeArr(heapEncoder.getSizeArrType());
     		lvalRepArr = heapEncoder.updateSizeArr(lvalRepArr, lval, rval);
        map.put(lSizeArrName, lvalRepArr);
     		String typeName = Identifiers.uniquify(DEFAULT_ALLOC_STATE_TYPE);
     		recordType = getRecordTypeFromMap(typeName, map);
    	} else {
    		lvalRepArr = map.get(lSizeArrName);
    		lvalRepArr = heapEncoder.updateSizeArr(lvalRepArr, lval, rval);
    		map.put(lSizeArrName, lvalRepArr);
    	}     	
      return exprManager.record(recordType, map.values());
    }
  }
  
  /**
   * Update side effect memory closure map
   * @param name
   * @param closure
   */
  private void updateSideEffectMemClosure(String name, ExpressionClosure closure) {
  	Preconditions.checkArgument(!sideEffectMemClosure.containsKey(name));
  	sideEffectMemClosure.put(name, closure);
  }
  
  /**
   * Update side effect size closure map
   * @param name
   * @param closure
   */
  private void updateSideEffectSizeClosure(String name, ExpressionClosure closure) {
  	Preconditions.checkArgument(!sideEffectSizeClosure.containsKey(name));
  	sideEffectSizeClosure.put(name, closure);
  }
  
  /**
   * Get the element memory array of <code>var</code>. If result array is stored
   * in side effect memory or side effect memory update closure, get such
   * entry from them, and evaluate the closure with <code>mem</code>, and return 
   * it. No fresh element is allowed.
   * @param mem
   * @param var
   * @return the element memory array of <code>var</code>
   */
  private ArrayExpression getMemArray(Expression state, String typeName) {
  	Preconditions.checkArgument(state.isTuple());
  	String arrName = getMemArrElemName(typeName);
  	ArrayExpression resMem = null;
    if(sideEffectMem.containsKey(arrName)) {
    	resMem = sideEffectMem.get(arrName);      
    } else if(sideEffectMemClosure.containsKey(arrName)) { 
    	ExpressionClosure resUpdate = sideEffectMemClosure.get(arrName);
    	resMem = resUpdate.eval(state).asArray();   	
    } else if(isElemInRecord(state.getChild(0), arrName)) {
    	resMem = selectRecordElem(state.getChild(0), arrName);
    } else {
    	throw new IllegalArgumentException("Not defined " + typeName);
    }   
    return resMem;
  }
  
  /**
   * Check if the memory array of <code>type</code> is defined, if not, create
   * a new one, and store it in side effect memory.
   * @param mem
   * @param var
   * @return <code>true</code> if updated, otherwise <code>false</code>
   */
  private boolean updateMemArray(Expression state, xtc.type.Type type, String typeName) {
  	Preconditions.checkArgument(state.isTuple());
  	String arrName = getMemArrElemName(typeName);
    if(sideEffectMem.containsKey(arrName) || 
    		sideEffectMemClosure.containsKey(arrName) || 
    		isElemInRecord(state.getChild(0), arrName)) {
    	return false;
    } else { // Fresh element
      Type valueType = heapEncoder.getArrayElemType(type);
      ArrayExpression resMem = getExpressionManager()
    			.arrayVar(arrName, addrType, valueType, false);
      sideEffectMem.put(arrName, resMem);
      return true;
    }
  }
  
  /**
   * Get the element memory array of <code>var</code>. If result array is stored
   * in side effect memory or side effect memory update closure, remove such
   * entry from them, and evaluate the closure with <code>mem</code>, and return 
   * it. For a fresh element, directly return it.
   * @param mem
   * @param var
   * @return resMem
   */
  private ArrayExpression popMemArray(Expression state, xtc.type.Type type, String typeName) {
  	Preconditions.checkArgument(state.isTuple());
  	String arrName = getMemArrElemName(typeName);
  	ArrayExpression resMem = null;
    if(sideEffectMem.containsKey(arrName)) {
    	resMem = sideEffectMem.remove(arrName);      
    } else if(sideEffectMemClosure.containsKey(arrName)) { 
    	ExpressionClosure resUpdate = sideEffectMemClosure.remove(arrName);
    	resMem = resUpdate.eval(state).asArray();   	
    } else if(isElemInRecord(state.getChild(0), arrName)) {
    	resMem = selectRecordElem(state.getChild(0), arrName);
    } else { // Fresh element
      Type valueType = heapEncoder.getArrayElemType(type);
      resMem = getExpressionManager()
    			.arrayVar(arrName, addrType, valueType, false);
    }   
    return resMem;
  }
  
  /**
   * Get the element size array of <code>var</code>. If result array is stored
   * in side effect size update closure, remove such entry from them, and 
   * evaluate the closure with <code>size</code>, and return it.
   * @param size
   * @param var
   * @return resSize
   */
  private ArrayExpression popSizeArray(Expression state, xtc.type.Type type, String typeName) {
  	Preconditions.checkArgument(state.isTuple());
  	while(type.hasShape() && type.getShape() instanceof FieldReference) {
  		Reference ref = type.getShape();
  		if(ref instanceof FieldReference) {
  			type = ref.getBase().getType();
  		}
  	} 	
  	
  	String arrName = getSizeArrElemName(typeName);
  	ArrayExpression resSize = null;
    if(sideEffectSizeClosure.containsKey(arrName)) { 
    	ExpressionClosure resUpdate = sideEffectSizeClosure.remove(arrName);
    	resSize = resUpdate.eval(state).asArray();   	
    } else if(isElemInRecord(state.getChild(1), arrName)) {
    	resSize = selectRecordElem(state.getChild(1), arrName);
    } else {
      resSize = heapEncoder.getConstSizeArr(heapEncoder.getSizeArrType());
    }
    return resSize;
  }
  
	/**
	 * Get the name of memory array element of <code>var</code>
	 * @param var
	 * @return the name of memory array of <code>var</code>
	 */
  private String getMemArrElemName(String name) {
  	StringBuilder sb = new StringBuilder()
  		.append(ARRAY_MEM_PREFIX)
    	.append(name);
  	String res = Identifiers.toValidId(sb.toString());
  	return res;
  }
  
	/**
	 * Get the name of size array element of <code>var</code>
	 * @param var
	 * @return the name of size array of <code>var</code>
	 */
  private String getSizeArrElemName(String name) {
    StringBuilder sb = new StringBuilder();
    sb.append(ARRAY_ALLOC_PREFIX)
    	.append(name);
  	String res = Identifiers.toValidId(sb.toString());
  	return res;
  }

	@Override
  public ExpressionClosure getCurrentState() {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public void clearCurrentState() {
	  // TODO Auto-generated method stub
	  
  }
}
