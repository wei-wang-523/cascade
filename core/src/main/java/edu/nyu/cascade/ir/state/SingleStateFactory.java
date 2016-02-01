package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

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
import edu.nyu.cascade.util.Pair;

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
		Expression region = createFreshRegion();
		BooleanExpression tt = getExpressionEncoding().tt().asBooleanExpression();
		updateMemState(state, ptr, ptrNode, region, null);
		updateSizeStateWithAlloc(state, ptr, region, size, ptrNode);
		updateMarkState(state, region, tt, ptrNode);
		
		plusRegionSize(state, size);
		state.addConstraint(applyValidMalloc(state, region, size, ptrNode));
	}
	
	@Override
	public void calloc(StateExpression state, Expression ptr, Expression nitem,
			Expression size, Node ptrNode) {
		ExpressionEncoding encoding = getExpressionEncoding();
		Expression multSize = encoding.times(nitem, size);
		Expression region = createFreshRegion();
		BooleanExpression tt = encoding.tt().asBooleanExpression();
		updateMemState(state, ptr, ptrNode, region, null);
		updateSizeStateWithAlloc(state, ptr, region, multSize, ptrNode);
		updateMarkState(state, region, tt, ptrNode);
		
		plusRegionSize(state, multSize);
		state.addConstraint(applyValidMalloc(state, region, multSize, ptrNode));
		state.addConstraint(applyMemset(state, region, multSize, 
				getExpressionEncoding().characterConstant(0),
				ptrNode));
	}
	
	@Override
	public void alloca(StateExpression state, Expression ptr, Expression size, Node ptrNode) {
		Expression region = createFreshRegion();
		updateMemState(state, ptr, ptrNode, region, null);
		updateSizeStateWithAlloc(state, ptr, region, size, ptrNode);
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
  public Expression cleanup(StateExpression state, Expression expr) {
  	Pair<Expression, Expression> pair1 = getCleanSizeSubstPair(state.asSingle());
  	Pair<Expression, Expression> pair2 = getCleanMarkSubstPair(state.asSingle());
    Expression exprPrime = expr.subst(
    		Lists.newArrayList(pair1.fst(), pair2.fst()), 
    		Lists.newArrayList(pair1.snd(), pair2.snd()));
    return exprPrime;
  }
  
  @Override
  public BooleanExpression applyMemset(StateExpression state, Expression region, 
  		Expression size, Expression value, Node ptrNode) {
  	Preconditions.checkArgument(state.isSingle());
  	IRDataFormatter formatter = getDataFormatter();
  	return formatter.memorySet(state.asSingle().getMemory(), region, size, value);
  }
  
  @Override
  public BooleanExpression applyMemcpy(StateExpression state, Expression destRegion, 
  		Expression srcRegion, Expression size, Node destNode, Node srcNode) {
  	Preconditions.checkArgument(state.isSingle());
  	
  	ArrayExpression mem = state.asSingle().getMemory();
  	IRDataFormatter formatter = getDataFormatter();
  	return formatter.memoryCopy(mem, mem, destRegion, srcRegion, size);
  }
	
	@Override
  public BooleanExpression applyValidMalloc(StateExpression state, Expression region, Expression size, Node ptrNode) {
		Preconditions.checkArgument(state.isSingle());
		Preconditions.checkNotNull(heapEncoder);		
		return heapEncoder.validMalloc(state.asSingle().getSize(), region, size);
  }
	
	@Override
	public BooleanExpression applyValidFree(StateExpression state, Expression region, Node ptrNode) {
		Preconditions.checkArgument(state.isSingle());
		Preconditions.checkNotNull(heapEncoder);
		return heapEncoder.validFree(state.asSingle().getMark(), region);
	}
	
	@Override
  public BooleanExpression validAccess(StateExpression state, Expression ptr, Node ptrNode) {
		Preconditions.checkArgument(state.isSingle());
		Preconditions.checkNotNull(heapEncoder);
		return getExpressionManager().or(
				heapEncoder.validMemAccess(state.asSingle().getSize(), ptr));
	}
	
  @Override
  public BooleanExpression validAccessRange(StateExpression state, Expression ptr, Expression size, Node ptrNode) {
		Preconditions.checkArgument(state.isSingle());
		Preconditions.checkNotNull(heapEncoder);
		return getExpressionManager().or(
				heapEncoder.validMemAccess(state.asSingle().getSize(), ptr, size));
  }
	
  @Override
  public BooleanExpression getDisjointAssumption(StateExpression state) {
		Preconditions.checkArgument(state.isSingle());
		Preconditions.checkNotNull(heapEncoder);
		return getExpressionManager().and(
				heapEncoder.disjointMemLayout(state.asSingle().getSize()));
  }
	
	@Override
  public SingleStateExpression freshState() {
    IRDataFormatter formatter = getDataFormatter();
    ArrayExpression memVar = formatter.getMemoryArrayType().variable(DEFAULT_MEMORY_VARIABLE_NAME + 
    		DEFAULT_STATE_NAME, false);
    ArrayExpression sizeVar = formatter.getSizeArrayType().variable(DEFAULT_SIZE_VARIABLE_NAME + 
    		DEFAULT_STATE_NAME, false);
    ArrayExpression markVar = formatter.getMarkArrayType().variable(DEFAULT_MARK_VARIABLE_NAME +
    		DEFAULT_STATE_NAME, false);
    return SingleStateExpression.create(DEFAULT_STATE_NAME, memVar, sizeVar, markVar);
  }
	
	@Override
	public void addStackVar(StateExpression state, Expression lval, IRVarInfo info) {
		Preconditions.checkNotNull(heapEncoder);
		heapEncoder.addFreshAddress(lval, info);
	}
	
  @Override
  public SingleStateExpression copy(StateExpression state) {
  	Preconditions.checkArgument(state.isSingle());
  	SingleStateExpression singleState = state.asSingle();
		SingleStateExpression newState = SingleStateExpression.create(
				singleState.getName(), singleState.getMemory(), singleState.getSize(), singleState.getMark());
		newState.setConstraint(state.getConstraint());
		newState.setGuard(state.getGuard());
		newState.setProperties(state.getProperties());
    return newState;
  }

	@Override
	public void propagateState(StateExpression cleanState,
	    StateExpression stateVar, StateExpression stateArg) {
		substitute(cleanState, stateVar, stateArg);
		cleanState.addPreGuard(stateArg.getGuard());
		cleanState.addConstraint(stateArg.getConstraint());
	}

	@Override
	public void initializeDefault(StateExpression state, Expression lval,
			Node lNode) {
		Preconditions.checkArgument(state.isSingle());
		SingleStateExpression singleState = state.asSingle();
		
		IRDataFormatter formatter = getDataFormatter();
		ArrayExpression memoryPrime = formatter.initializeZero(
				singleState.getMemory(), lval, CType.getType(lNode));
		singleState.setMemory(memoryPrime);
	}
	
	@Override
	public void initializeValues(StateExpression state, Expression lval,
			Node lNode, List<Expression> rvals, List<Node> rNodes) {
		Preconditions.checkArgument(state.isSingle());
		SingleStateExpression singleState = state.asSingle();
		
		List<xtc.type.Type> rTypes = Lists.newArrayList();
		for(Node rNode : rNodes) rTypes.add(CType.getType(rNode));
		
		IRDataFormatter formatter = getDataFormatter();
		ArrayExpression memoryPrime = formatter.initializeValues(
				singleState.getMemory(), lval, CType.getType(lNode), rvals, rTypes);
		singleState.setMemory(memoryPrime);
	}
	
	@Override
	protected Expression getSizeOfRegion(StateExpression state, Expression region, Node ptrNode) {
		Preconditions.checkArgument(state.isSingle());
		SingleStateExpression singleState = state.asSingle();
		ArrayExpression sizeArr = singleState.getSize();
		return getDataFormatter().indexSizeArray(sizeArr, region);
	}

	@Override
	protected void updateMemState(StateExpression state, 
			Expression index, Node idxNode, Expression value, @Nullable Node valNode) {
		Preconditions.checkArgument(state.isSingle());
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
	protected void updateSizeState(StateExpression state, 
			Expression region, Expression size, Node ptrNode) {
		Preconditions.checkArgument(state.isSingle());
		
		SingleStateExpression singleState = state.asSingle();
		IRDataFormatter formatter = getDataFormatter();
		ArrayExpression sizePrime = formatter.updateSizeArray(
	  		singleState.getSize(), region, size);
	  singleState.setSize(sizePrime);
	}
	
	@Override
	protected void updateMarkState(StateExpression state, 
			Expression region, BooleanExpression mark, Node ptrNode) {
		Preconditions.checkArgument(state.isSingle());
		
		SingleStateExpression singleState = state.asSingle();
		ArrayExpression markPrime = singleState.getMark().update(region, mark);
	  singleState.setMark(markPrime);
	}

	/** <code>ptr</code> and <code>ptrNode</code> is not used here */
	@Override
	protected void updateSizeStateWithAlloc(StateExpression state,
	    Expression ptr, Expression region, Expression size, Node ptrNode) {
		Preconditions.checkArgument(state.isSingle());
		Preconditions.checkNotNull(heapEncoder);
		
		SingleStateExpression singleState = state.asSingle();
		
		IRDataFormatter formatter = getDataFormatter();
	  ArrayExpression sizePrime = formatter.updateSizeArray(
	  		singleState.getSize(), region, size);
	  singleState.setSize(sizePrime);
		heapEncoder.addFreshRegion(region);
	}

	@Override
	protected void propagateProperties(StateExpression fromState, StateExpression toState) {
	}

	@Override
	protected Pair<List<Expression>, List<Expression>> getSubstElemsPair(
			StateExpression fromState, StateExpression toState) {
		int elemSize = fromState.asSingle().getElemSize();
		List<Expression> fromElems = Lists.newArrayListWithCapacity(elemSize);
		List<Expression> toElems = Lists.newArrayListWithCapacity(elemSize);
		
		ArrayExpression fromMem = fromState.asSingle().getMemory();
		ArrayExpression toMem = toState.asSingle().getMemory();
		if(!fromMem.equals(toMem)) {
			fromElems.add(fromMem); toElems.add(toMem);
		}

		ArrayExpression fromSize = fromState.asSingle().getSize();
		ArrayExpression toSize = toState.asSingle().getSize();
		if(!fromSize.equals(toSize)) {
			fromElems.add(fromSize); toElems.add(toSize);
		}
		
		ArrayExpression fromMark = fromState.asSingle().getMark();
		ArrayExpression toMark = toState.asSingle().getMark();
		if(!fromMark.equals(toMark)) {
			fromElems.add(fromMark); toElems.add(toMark);
		}
		
		return Pair.of(fromElems, toElems);
	}
	
	@Override
	protected Pair<List<Expression>, List<Expression>> getSubstPredicatesPair(
			StateExpression fromState, StateExpression toState) {
		return Pair.of(Collections.<Expression>emptyList(), Collections.<Expression>emptyList());
	}

	@Override
	protected void doSubstitute(StateExpression state,
			final Collection<Expression> fromElems, 
			final Collection<Expression> toElems,
			Collection<Expression> fromPredicates, 
			Collection<Expression> toPredicates) {
		Preconditions.checkArgument(state.isSingle());
		
		if(fromElems.isEmpty())		return;
		
		SingleStateExpression singleState = state.asSingle();
		
		/* Substitute state elements */
		Expression newMem = singleState.getMemory().subst(fromElems, toElems);
		Expression newSize = singleState.getSize().subst(fromElems, toElems);
		Expression newMark = singleState.getMark().subst(fromElems, toElems);
		singleState.setMemory(newMem.asArray());
		singleState.setSize(newSize.asArray());
		singleState.setMark(newMark.asArray());
    
    if(state.getConstraint() != null) { /* Substitute constraint */
    	Expression pc = state.getConstraint();
    	BooleanExpression pcPrime = pc.subst(fromElems, toElems).asBooleanExpression();
    	state.setConstraint(pcPrime);
    }
    
    { /* Substitute guards */
    	Expression guard = state.getGuard();
    	BooleanExpression guardPrime = guard.subst(fromElems, toElems).asBooleanExpression();
    	state.setGuard(guardPrime);
    }
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
	protected void substitute(StateExpression state, 
			StateExpression stateVar, StateExpression stateArg) {
		Pair<List<Expression>, List<Expression>> substElemsPair = 
				getSubstElemsPair(stateVar, stateArg);
		Pair<List<Expression>, List<Expression>> substPredsPair =
				getSubstPredicatesPair(state, stateArg);
		
		doSubstitute(state, 
				substElemsPair.fst(),
				substElemsPair.snd(), 
				substPredsPair.fst(), 
				substPredsPair.snd());
	}
	
	@Override
	protected Expression dereference(StateExpression state, Expression index, Node indexNode) {
		Preconditions.checkArgument(state.isSingle());
		xtc.type.Type idxType = CType.getType(indexNode);
		return getDataFormatter().indexMemoryArray(state.asSingle().getMemory(), index, idxType);
	}

	@Override
	protected Expression eval(Expression expr, StateExpression stateVar,
	    final StateExpression state) {
		Preconditions.checkArgument(stateVar.isSingle());
		Preconditions.checkArgument(state.isSingle());
		
		Pair<List<Expression>, List<Expression>> sustElemsPair = 
				getSubstElemsPair(stateVar, state);
		List<Expression> fromExprs = sustElemsPair.fst();
		List<Expression> toExprs = sustElemsPair.snd();
		
		Expression exprPrime = fromExprs.isEmpty() ? expr : expr.subst(fromExprs, toExprs);
		return exprPrime;
	}

	SingleStateExpression freshSingleState(String labelName, xtc.type.Type type) {
		Preconditions.checkNotNull(type);
	  ExpressionManager exprManager = getExpressionManager();
	  IRDataFormatter formatter = getDataFormatter();
	  ArrayExpression memVar = exprManager.arrayType(
	  		formatter.getAddressType(), formatter.getArrayElemType(type)).variable(
	  				DEFAULT_MEMORY_VARIABLE_NAME + labelName, true);
	  ArrayExpression sizeVar = formatter.getSizeArrayType().variable(
	  		DEFAULT_SIZE_VARIABLE_NAME + labelName, true);
	  ArrayExpression markVar = formatter.getMarkArrayType().variable(
	  		DEFAULT_MARK_VARIABLE_NAME + labelName, true);
	  return SingleStateExpression.create(labelName, memVar, sizeVar, markVar);
	}
	
	void copyProperties(SingleStateExpression fromState, SingleStateExpression toState) {	
		toState.setProperties(fromState.getProperties());
		toState.setConstraint(fromState.getConstraint());
		toState.setGuard(fromState.getGuard());
	}

	/**
	 * Collection the substitution pair of size variable cleaning
	 * @param state
	 * @return
	 */
	Pair<Expression, Expression> getCleanSizeSubstPair(SingleStateExpression state) {
		Preconditions.checkArgument(state.isSingle());
		ExpressionManager exprManager = getExpressionManager();
		IRDataFormatter formatter = getDataFormatter();
		String labelName = state.asSingle().getName();
	  Expression sizeVar = exprManager.variable(DEFAULT_SIZE_VARIABLE_NAME + labelName, 
	      formatter.getSizeArrayType(), false);
		Expression constSizeArr = getConstSizeArr(formatter.getSizeArrayType());
		return Pair.of(sizeVar, constSizeArr);
	}

	Pair<Expression, Expression> getCleanMarkSubstPair(
			SingleStateExpression state) {
		ExpressionManager exprManager = getExpressionManager();
		IRDataFormatter formatter = getDataFormatter();
		String labelName = state.asSingle().getName();
	  Expression markVar = exprManager.variable(DEFAULT_MARK_VARIABLE_NAME + labelName, 
	      formatter.getMarkArrayType(), false);
		Expression constMarkArr = getConstMarkArr(formatter.getMarkArrayType());
		return Pair.of(markVar, constMarkArr);
	}
}

