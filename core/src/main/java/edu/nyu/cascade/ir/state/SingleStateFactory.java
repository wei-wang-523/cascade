package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;

import javax.annotation.Nullable;

import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Lists;
import com.google.inject.Inject;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.IRSingleHeapEncoder;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;

public class SingleStateFactory<T> extends AbstractStateFactory<T> {
	
	private static final String DEFAULT_STATE_NAME = "flat";
	
	private final IRSingleHeapEncoder heapEncoder;
	
	@Inject
	SingleStateFactory(ExpressionEncoding encoding, IRDataFormatter formatter, IRSingleHeapEncoder singleHeapEncoder) {
	  super(encoding, formatter);
	  heapEncoder = singleHeapEncoder;
  }
	
	@Override
	public void reset() {
		heapEncoder.reset();
	}
	
	@Override
	public <X> void setLabelAnalyzer(PreProcessor<X> preprocessor) {
		throw new UnsupportedOperationException();
	}
	
	@Override
	public void malloc(StateExpression state, Expression ptr, Expression size, Node ptrNode) {		
		VariableExpression region = createFreshRegion();
		state.addRegion(region);
		BooleanExpression tt = getExpressionEncoding().tt().asBooleanExpression();
		updateMemState(state, ptr, ptrNode, region, null);
		updateSizeStateWithAlloc(state, region, size, ptrNode);
		updateMarkState(state, region, tt, ptrNode);
		
		plusRegionSize(state, size);
		state.addConstraint(applyValidMalloc(state, region, size, ptrNode));
	}
	
	@Override
	public void calloc(StateExpression state, Expression ptr, Expression nitem,
			Expression size, Node ptrNode) {
		ExpressionEncoding encoding = getExpressionEncoding();
		Expression multSize = encoding.times(nitem, size);
		VariableExpression region = createFreshRegion();
		state.addRegion(region);
		BooleanExpression tt = encoding.tt().asBooleanExpression();
		updateMemState(state, ptr, ptrNode, region, null);
		updateSizeStateWithAlloc(state, region, multSize, ptrNode);
		updateMarkState(state, region, tt, ptrNode);
		
		plusRegionSize(state, multSize);
		state.addConstraint(applyValidMalloc(state, region, multSize, ptrNode));
		state.addConstraint(applyMemset(state, region, multSize, 
				getExpressionEncoding().characterConstant(0),
				ptrNode));
	}
	
	@Override
	public void alloca(StateExpression state, Expression ptr, Expression size, Node ptrNode) {
		VariableExpression region = createFreshRegion();
		state.addRegion(region);
		updateMemState(state, ptr, ptrNode, region, null);
		updateSizeStateWithAlloc(state, region, size, ptrNode);
		state.addConstraint(applyValidMalloc(state, region, size, ptrNode));
	}
	
  @Override
	public SingleStateExpression resolvePhiNode(Collection<StateExpression> preStates) {
  	/* Build the joined state */
  	Iterable<BooleanExpression> preGuards = Iterables.transform(preStates, pickGuard);
  	SingleStateExpression joinState = joinPreStates(preStates, preGuards);
  	
  	/* Set the constraint and guard */
  	BooleanExpression joinConstraint = joinConstraints(preStates);
    joinState.setConstraint(joinConstraint);
    BooleanExpression joinGuard = joinGuards(preStates);
    joinState.setGuard(joinGuard);
    
    /* Set the memory tracker */
		joinMemTrackers(joinState, preStates);
		
    return joinState;
	}
  
  @Override
  public BooleanExpression applyMemset(StateExpression state, Expression region, 
  		Expression size, Expression value, Node ptrNode) {
  	IRDataFormatter formatter = getDataFormatter();
  	return formatter.memorySet(state.asSingle().getMemory(), region, size, value);
  }
  
  @Override
  public BooleanExpression applyMemset(StateExpression state, Expression region, 
  		Expression size, int value, Node ptrNode) {
  	IRDataFormatter formatter = getDataFormatter();
  	return formatter.memorySet(state.asSingle().getMemory(), region, size, value);
  }
  
  @Override
  public BooleanExpression applyMemcpy(StateExpression state, Expression destRegion, 
  		Expression srcRegion, Expression size, Node destNode, Node srcNode) {
  	ArrayExpression mem = state.asSingle().getMemory();
  	IRDataFormatter formatter = getDataFormatter();
  	return formatter.memoryCopy(mem, mem, destRegion, srcRegion, size);
  }
	
	@Override
  public BooleanExpression applyValidMalloc(StateExpression state, Expression region, 
  		Expression size, Node ptrNode) {
		Preconditions.checkNotNull(heapEncoder);		
		return heapEncoder.validMalloc(state.asSingle().getSize(), region, size);
  }
	
	@Override
	public BooleanExpression applyValidFree(StateExpression state, Expression region, Node ptrNode) {
		Preconditions.checkNotNull(heapEncoder);
		return heapEncoder.validFree(state.asSingle().getMark(), region);
	}
	
	@Override
  public BooleanExpression validAccess(StateExpression state, Expression ptr, Node ptrNode) {
		Preconditions.checkNotNull(heapEncoder);
		return getExpressionManager().or(
				heapEncoder.validMemAccess(state.asSingle().getSize(), ptr));
	}
	
  @Override
  public BooleanExpression validAccessRange(StateExpression state, Expression ptr, 
  		Expression size, Node ptrNode) {
		Preconditions.checkNotNull(heapEncoder);
		return getExpressionManager().or(
				heapEncoder.validMemAccess(state.asSingle().getSize(), ptr, size));
  }
	
  @Override
  public SingleStateExpression freshState() {
    SingleStateExpression freshState = freshSingleState();
	  freshState.setMemTracker(getDataFormatter().getSizeZero());
	  return freshState;
  }
	
	@Override
	public void addStackVar(StateExpression state, Expression lval, IRVarInfo info) {
		Preconditions.checkNotNull(heapEncoder);
		if(!info.isStatic()) state.addVar(lval.asVariable());
		heapEncoder.addFreshAddress(lval, info);
	}
	
	@Override
	public void addStackVarArray(StateExpression state, Expression lval, 
			Expression rval, IRVarInfo info, Node sourceNode) {
		Preconditions.checkNotNull(heapEncoder);
		if(!info.isStatic()) state.addVar(lval.asVariable());
		updateSizeStateWithAlloc(state, lval, rval, sourceNode);
		state.addConstraint(applyValidMalloc(state, lval, rval, sourceNode));
	}
	
  @Override
  public SingleStateExpression copy(StateExpression state) {
  	SingleStateExpression singleState = state.asSingle();
		SingleStateExpression newState = SingleStateExpression.create(
				singleState.getName(), singleState.getMemory(), singleState.getSize(), singleState.getMark());
		newState.setConstraint(state.getConstraint());
		newState.setGuard(state.getGuard());
		newState.setProperties(state.getProperties());
		newState.addVars(state.getVars());
		newState.addRegions(state.getRegions());
		newState.setAssertions(state.getAssertions());
		newState.setMemTracker(state.getMemTracker());
    return newState;
  }
  
  @Override
  public void substitute(StateExpression state,
  		Collection<? extends Expression> vars, Collection<? extends Expression> freshVars) {
		substState(state, vars, freshVars);
		substConstraintGuard(state, vars, freshVars);
		substAssertions(state, vars, freshVars);
		substMemTracker(state, vars, freshVars);
  }

	@Override
	public void propagateState(StateExpression cleanState, StateExpression stateArg) {
		Collection<Expression> fromElems = Lists.newArrayList();
		Collection<Expression> toElems = Lists.newArrayList();
		
		getSubstElemsPair(cleanState, stateArg, fromElems, toElems);
		substitute(cleanState, fromElems, toElems);
		
		cleanState.addPreGuard(stateArg.getGuard());
		cleanState.addConstraint(stateArg.getConstraint());
		
		propagateAssertions(stateArg, cleanState);
		propagateMemTracker(stateArg, cleanState);
	}
	
	@Override
	public Collection<BooleanExpression> getAssumptions() {
		return Collections.emptyList();
	}
	
	@Override
	public Expression lookupSize(StateExpression state, Expression ptr, Node node) {
		return getDataFormatter().indexSizeArray(state.asSingle().getSize(), ptr);
	}

	@Override
	protected BooleanExpression getDisjointAssumption(StateExpression state) {
		Preconditions.checkNotNull(heapEncoder);
		return getExpressionManager().and(
				heapEncoder.disjointMemLayout(state.asSingle().getSize()));
	}

	@Override
	protected Expression getSizeOfRegion(StateExpression state, Expression region, Node ptrNode) {
		SingleStateExpression singleState = state.asSingle();
		ArrayExpression sizeArr = singleState.getSize();
		return getDataFormatter().indexSizeArray(sizeArr, region);
	}

	@Override
	protected void updateMemState(StateExpression state, 
			Expression index, Node idxNode, Expression value, @Nullable Node valNode) {
		SingleStateExpression singleState = state.asSingle();
		
		IRDataFormatter formatter = getDataFormatter();
		xtc.type.Type idxType = CType.getType(idxNode);
		xtc.type.Type valType = valNode != null ? CType.getType(valNode) : null;
		ArrayExpression memoryPrime = formatter.updateMemoryArray(
				singleState.getMemory(), index, idxType, value, valType);
		singleState.setMemory(memoryPrime);
	}
	
	/** <code>ptrNode</code> is not used here*/
	@Override
	protected void updateSizeStateWithFree(StateExpression state, 
			Expression region, Expression size, Node ptrNode) {
		SingleStateExpression singleState = state.asSingle();
		IRDataFormatter formatter = getDataFormatter();
		ArrayExpression sizePrime = formatter.updateSizeArray(
	  		singleState.getSize(), region, size);
	  singleState.setSize(sizePrime);
	}
	
	@Override
	protected void updateMarkState(StateExpression state, 
			Expression region, BooleanExpression mark, Node ptrNode) {
		SingleStateExpression singleState = state.asSingle();
		// FIXME: update size array only if region is not nullptr
		ArrayExpression markPrime = singleState.getMark().update(region, mark);
	  singleState.setMark(markPrime);
	}

	/** <code>ptr</code> and <code>ptrNode</code> is not used here */
	@Override
	protected void updateSizeStateWithAlloc(StateExpression state,
	    Expression region, Expression size, Node ptrNode) {
		Preconditions.checkNotNull(heapEncoder);
		
		SingleStateExpression singleState = state.asSingle();
		//FIXME: update size array only if region is not nullptr
		IRDataFormatter formatter = getDataFormatter();
	  ArrayExpression sizePrime = formatter.updateSizeArray(
	  		singleState.getSize(), region, size);
	  singleState.setSize(sizePrime);
		heapEncoder.addFreshRegion(region);
	}

	@Override
	protected void propagateMemSafetyPredicates(StateExpression fromState, StateExpression toState) {
	}

	@Override
	protected void getSubstElemsPair(
			StateExpression fromState, StateExpression toState,
			Collection<Expression> fromElems, Collection<Expression> toElems) {
		
		SingleStateExpression fromStateVar = getStateVar(fromState.asSingle());
		
		ArrayExpression fromMem = fromStateVar.getMemory();
		ArrayExpression toMem = toState.asSingle().getMemory();
		if(!fromMem.equals(toMem)) {
			fromElems.add(fromMem); toElems.add(toMem);
		}

		ArrayExpression fromSize = fromStateVar.getSize();
		ArrayExpression toSize = toState.asSingle().getSize();
		if(!fromSize.equals(toSize)) {
			fromElems.add(fromSize); toElems.add(toSize);
		}
		
		ArrayExpression fromMark = fromStateVar.getMark();
		ArrayExpression toMark = toState.asSingle().getMark();
		if(!fromMark.equals(toMark)) {
			fromElems.add(fromMark); toElems.add(toMark);
		}
	}
	
	@Override
	protected void getSubstPredicatesPair(
			StateExpression fromState, StateExpression toState, 
			Collection<Expression> fromPredicates, Collection<Expression> toPredicates) {
		return;
	}

	@Override
	protected void substState(StateExpression state,
			Collection<? extends Expression> fromElems, Collection<? extends Expression> toElems) {
		if(fromElems.isEmpty())		return;
		
		SingleStateExpression singleState = state.asSingle();
		
		/* Substitute state elements */
		Expression newMem = singleState.getMemory().subst(fromElems, toElems);
		Expression newSize = singleState.getSize().subst(fromElems, toElems);
		Expression newMark = singleState.getMark().subst(fromElems, toElems);
		singleState.setMemory(newMem.asArray());
		singleState.setSize(newSize.asArray());
		singleState.setMark(newMark.asArray());
	}

	@Override
	protected SingleStateExpression joinPreStates(Iterable<StateExpression> preStates,
			Iterable<BooleanExpression> preGuards) {
	  Preconditions.checkArgument(Iterables.size(preStates) == Iterables.size(preGuards));
	  
	  SingleStateExpression firstPreState = preStates.iterator().next().asSingle();
	  
	  LinkedHashMultimap<Expression, BooleanExpression> guardMemMap = LinkedHashMultimap.create();
	  LinkedHashMultimap<Expression, BooleanExpression> guardSizeMap = LinkedHashMultimap.create();
	  LinkedHashMultimap<Expression, BooleanExpression> guardMarkMap = LinkedHashMultimap.create();
  	Iterator<BooleanExpression> preGuardItr = preGuards.iterator();
  	for(StateExpression preState : preStates) {
  		BooleanExpression preGuard = preGuardItr.next();
  		Expression preMem = preState.asSingle().getMemory();
  		Expression preSize = preState.asSingle().getSize();
  		Expression preMark = preState.asSingle().getMark();
  		guardMemMap.put(preMem, preGuard);
  		guardSizeMap.put(preSize, preGuard);
  		guardMarkMap.put(preMark, preGuard);
  	}
  	
  	ArrayExpression joinStateMem = getITEExpression(guardMemMap).asArray();
  	ArrayExpression joinStateSize = getITEExpression(guardSizeMap).asArray();
  	ArrayExpression joinStateMark = getITEExpression(guardMarkMap).asArray();
	
	  final String preStateName = firstPreState.getName();
	  
	  assert(Iterables.all(preStates, new Predicate<StateExpression>(){
			@Override
	    public boolean apply(StateExpression state) {
	      return state.asSingle().getName().equals(preStateName);
	    }
	  }));
	  
	  return SingleStateExpression.create(preStateName, joinStateMem, joinStateSize, joinStateMark);
	}
	
	@Override
	protected Expression dereference(StateExpression state, Expression index, Node indexNode) {
		xtc.type.Type idxType = CType.getType(indexNode);
		return getDataFormatter().indexMemoryArray(state.asSingle().getMemory(), index, idxType);
	}

	@Override
	protected void substSafetyPredicates(StateExpression state,
			Collection<? extends Expression> fromElems, Collection<? extends Expression> toElems) {
	  // TODO Auto-generated method stub
	  
	}
	
	SingleStateExpression freshSingleState() {
    IRDataFormatter formatter = getDataFormatter();
    ArrayExpression memVar = formatter.getMemoryArrayType().variable(DEFAULT_MEMORY_VARIABLE_NAME + 
    		DEFAULT_STATE_NAME, false);
    ArrayExpression sizeVar = formatter.getSizeArrayType().variable(DEFAULT_SIZE_VARIABLE_NAME + 
    		DEFAULT_STATE_NAME, false);
    ArrayExpression markVar = formatter.getMarkArrayType().variable(DEFAULT_MARK_VARIABLE_NAME +
    		DEFAULT_STATE_NAME, false);
    
    ExpressionEncoding encoding = getExpressionEncoding();
    encoding.addAssumption(sizeVar.index(formatter.getNullAddress()).eq(formatter.getSizeZero()));
    encoding.addAssumption(markVar.index(formatter.getNullAddress()).eq(encoding.tt()));
    
    return SingleStateExpression.create(DEFAULT_STATE_NAME, memVar, sizeVar, markVar);
	}

	SingleStateExpression freshSingleState(String labelName, long width) {
	  ExpressionManager exprManager = getExpressionManager();
	  IRDataFormatter formatter = getDataFormatter();
	  ArrayExpression memVar = exprManager.arrayType(
	  		formatter.getAddressType(), formatter.getArrayElemType(width)).variable(
	  				DEFAULT_MEMORY_VARIABLE_NAME + labelName, false);
	  ArrayExpression sizeVar = formatter.getSizeArrayType().variable(
	  		DEFAULT_SIZE_VARIABLE_NAME + labelName, false);
	  ArrayExpression markVar = formatter.getMarkArrayType().variable(
	  		DEFAULT_MARK_VARIABLE_NAME + labelName, false);
	  
    ExpressionEncoding encoding = getExpressionEncoding();
    encoding.addAssumption(sizeVar.index(formatter.getNullAddress()).eq(formatter.getSizeZero()));
    encoding.addAssumption(markVar.index(formatter.getNullAddress()).eq(encoding.tt()));
    
	  return SingleStateExpression.create(labelName, memVar, sizeVar, markVar);
	}
	
	SingleStateExpression freshSingleState(String labelName, ArrayType[] elemTypes) {
		Preconditions.checkArgument(elemTypes.length == 3);
	  ArrayExpression memVar = elemTypes[0].variable(DEFAULT_MEMORY_VARIABLE_NAME + 
	  		labelName, false);
	  ArrayExpression sizeVar = elemTypes[1].variable(DEFAULT_SIZE_VARIABLE_NAME + 
	  		labelName, false);
	  ArrayExpression markVar = elemTypes[2].variable(DEFAULT_MARK_VARIABLE_NAME +
	  		labelName, false);
	  return SingleStateExpression.create(labelName, memVar, sizeVar, markVar);
	}
	
	void copyProperties(SingleStateExpression fromState, SingleStateExpression toState) {	
		toState.setProperties(fromState.getProperties());
		toState.setConstraint(fromState.getConstraint());
		toState.setGuard(fromState.getGuard());
	}
	
	void updateStructInMemState(StateExpression state, 
			Expression index, Expression value, long range) {
		SingleStateExpression singleState = state.asSingle();
		IRDataFormatter formatter = getDataFormatter();
		ArrayExpression memoryPrime = formatter.updateStructInMemoryArray(
				singleState.getMemory(), index, value, range);
		singleState.setMemory(memoryPrime);
	}
	
	private SingleStateExpression getStateVar(SingleStateExpression state) {
		String labelName = state.getName();
		ArrayType[] elemTypes = state.getElemTypes();
		return freshSingleState(labelName, elemTypes);
	}
}

