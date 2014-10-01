package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Collections;
import java.util.List;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.inject.Inject;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.IRSingleHeapEncoder;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;

public class SingleStateFactory<T> extends AbstractStateFactory<T> {
	
	private static final String DEFAULT_MEMORY_VARIABLE_NAME = "m";
	private static final String DEFAULT_SIZE_VARIABLE_NAME = "size";
	private static final String DEFAULT_STATE_NAME = "flat";
	private static final String ConstArray = "constArr";
	private static final String IndexVar = "indexVar";
	
	private final IRSingleHeapEncoder heapEncoder;
	
	@Inject
	SingleStateFactory(ExpressionEncoding encoding, IRDataFormatter formatter, IRSingleHeapEncoder singleHeapEncoder) {
	  super(encoding, formatter);
	  heapEncoder = singleHeapEncoder;
  }
	
	@Override
	public <X> void setLabelAnalyzer(PreProcessor<X> preprocessor) {
		throw new UnsupportedOperationException();
	}
	
	@Override
	public SingleStateExpression alloc(StateExpression state, Expression ptr, Expression size) {
		Expression region = createFreshRegion(ptr);
		SingleStateExpression state1 = updateMemState(state, ptr, region);
		SingleStateExpression state2 = updateSizeStateWithAlloc(state1, ptr, region, size);
		return state2;
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
    return joinState;
	}
  
  @Override
  public Expression cleanup(StateExpression state, Expression expr) {
  	Pair<Expression, Expression> pair = getCleanSizeSubstPair(state.asSingle());
    return expr.subst(pair.fst(), pair.snd());
  }
	
	@Override
  public Expression eval(Expression expr, StateExpression stateVar,
      final StateExpression state) {
		Preconditions.checkArgument(stateVar.isSingle());
		Preconditions.checkArgument(state.isSingle());
		
		Pair<List<Expression>, List<Expression>> sustElemsPair = 
				getSubstElemsPair(stateVar, state);
		List<Expression> fromExprs = sustElemsPair.fst();
		List<Expression> toExprs = sustElemsPair.snd();
		
		if(fromExprs.isEmpty()) return expr;
		
		return expr.subst(fromExprs, toExprs);
  }
	
	/** Do nothing */
	@Override
	public void propagateNewInfo(StateExpression fromState, StateExpression toState) {
	}

	@Override
  public Expression applyValidMalloc(StateExpression state, Expression ptr, Expression size) {
		Preconditions.checkArgument(state.isSingle());
		Preconditions.checkNotNull(heapEncoder);
		return heapEncoder.validMalloc(state.asSingle().getElement(1).asArray(), ptr, size);
  }
	
	@Override
	public BooleanExpression applyValidFree(StateExpression state, Expression ptr) {
		Preconditions.checkArgument(state.isSingle());
		Preconditions.checkNotNull(heapEncoder);
		return heapEncoder.validFree(state.asSingle().getElement(1).asArray(), ptr);
	}
	
	@Override
  public Expression validAccess(StateExpression state, Expression ptr) {
		Preconditions.checkArgument(state.isSingle());
		Preconditions.checkNotNull(heapEncoder);
		return getExpressionEncoding().or(
				heapEncoder.validMemAccess(
						state.asSingle().getElement(1).asArray(), ptr));
	}
	
  @Override
  public Expression validAccessRange(StateExpression state, Expression ptr, Expression size) {
		Preconditions.checkArgument(state.isSingle());
		Preconditions.checkNotNull(heapEncoder);
		return getExpressionEncoding().or(
				heapEncoder.validMemAccess(
						state.asSingle().getElement(1).asArray(), ptr, size));
  }
	
  @Override
  public Expression getDisjointAssumption(StateExpression state) {
		Preconditions.checkArgument(state.isSingle());
		Preconditions.checkNotNull(heapEncoder);
		return getExpressionEncoding().and(
				heapEncoder.disjointMemLayout(state.asSingle().getElement(1).asArray()));
  }
	
	@Override
  public SingleStateExpression freshState() {
    ExpressionManager exprManager = getExpressionManager();
    IRDataFormatter formatter = getDataFormatter();
    Expression memVar = exprManager.variable(DEFAULT_MEMORY_VARIABLE_NAME + 
    		Identifiers.UNDERLINE + DEFAULT_STATE_NAME, 
    		formatter.getMemoryArrayType(), false);
    Expression sizeVar = exprManager.variable(DEFAULT_SIZE_VARIABLE_NAME + 
    		Identifiers.UNDERLINE + DEFAULT_STATE_NAME, 
        formatter.getSizeArrayType(), false);
    return SingleStateExpression.create(DEFAULT_STATE_NAME, memVar, sizeVar);
  }
	
	@Override
  public SingleStateExpression updateMemState(StateExpression state, 
  		Expression memIdx, Expression memVal) {
  	Preconditions.checkArgument(state.isSingle());
  	SingleStateExpression singleState = state.asSingle();
  	
  	IRDataFormatter formatter = getDataFormatter();
  	
  	Expression memory = formatter.updateMemoryArray(
  			singleState.getElement(0).asArray(), memIdx, memVal);
    Expression size = singleState.getElement(1);
    
    SingleStateExpression resState = SingleStateExpression.create(singleState.getName(), 
    		memory, size);
		copyProperties(singleState, resState);
    return resState;
  }
  
  @Override
  public SingleStateExpression updateSizeState(StateExpression state, 
  		Expression sizeIdx, Expression sizeVal) {
  	Preconditions.checkArgument(state.isSingle());
  	SingleStateExpression singleState = state.asSingle();
  	
  	IRDataFormatter formatter = getDataFormatter();
  	
  	Expression memory = singleState.getElement(0);
    Expression size = formatter.updateSizeArray(
    		singleState.getElement(1).asArray(), sizeIdx, sizeVal);
    
    SingleStateExpression resState = SingleStateExpression.create(singleState.getName(), 
    		memory, size);
		copyProperties(singleState, resState);
    return resState;
  }
	
	@Override
	public Expression deref(StateExpression state, Expression index) {
		Preconditions.checkArgument(state.isSingle());
		return getDataFormatter().indexMemoryArray(
	  		state.asSingle().getElement(0).asArray(), index);
	}
	
	@Override
	public SingleStateExpression addStackVar(StateExpression state, Expression lval, IRVarInfo info) {
		Preconditions.checkNotNull(heapEncoder);
		heapEncoder.addFreshAddress(lval, info);
		return state.asSingle();
	}
	
	/** Do nothing */
	@Override
	public StateExpression scopeOptimize(StateExpression preState, 
			StateExpression postState) {
		return postState;
	}

	@Override
	public StateExpression propagateState(StateExpression cleanState,
	    StateExpression stateVar, StateExpression stateArg) {
		StateExpression statePrime = substitute(cleanState, stateVar, stateArg);
		propagateProperties(stateArg, statePrime);
		return statePrime;
	}

	@Override
	protected void propagateProperties(StateExpression fromState, StateExpression toState) {    
	  /* Propagate fromState guard to toState, guard contains 
	   * no valid_access or valid_access_range */
	  if(fromState.hasGuard()) {
	  	BooleanExpression fromGuard = fromState.getGuard();
	  	toState.addGuard(fromGuard);
	  }
		
	  /* Propagate fromState constraint to toState, constraint may contain 
	   * valid_access and valid_access_range */
	  if(fromState.hasConstraint()) {
	  	BooleanExpression fromConstraint = fromState.getConstraint();
	  	ExpressionManager exprManager = getExpressionManager();
	  	toState.addConstraint(fromConstraint, exprManager.tt(), exprManager.ff());
	  }
	}

	/** <code>ptr</code> is not used here */
	@Override
	protected SingleStateExpression updateSizeStateWithAlloc(StateExpression state,
	    Expression ptr, Expression region, Expression size) {
  	Preconditions.checkArgument(state.isSingle());
		Preconditions.checkNotNull(heapEncoder);
		
  	SingleStateExpression singleState = state.asSingle();
  	
  	IRDataFormatter formatter = getDataFormatter();
    Expression sizePrime = formatter.updateSizeArray(
    		singleState.getElement(1).asArray(), region, size);
    
    SingleStateExpression resState = SingleStateExpression.create(
    		singleState.getName(), singleState.getElement(0), sizePrime);
		copyProperties(singleState, resState);
		heapEncoder.addFreshRegion(region);
    return resState;
	}
	
	@Override
	protected Pair<List<Expression>, List<Expression>> getSubstElemsPair(
			StateExpression fromState, StateExpression toState, boolean fetchFreshMap) {
		int elemSize = fromState.asSingle().getElemSize();
		List<Expression> fromElems = Lists.newArrayListWithCapacity(elemSize);
		List<Expression> toElems = Lists.newArrayListWithCapacity(elemSize);
		
		for(int i = 0; i < elemSize; i++) {
			Expression fromExpr = fromState.asSingle().getElement(i);
			Expression toExpr = toState.asSingle().getElement(i);
			if(fromExpr.equals(toExpr)) continue;
			fromElems.add(fromExpr); toElems.add(toExpr);
		}
		
		return Pair.of(fromElems, toElems);
	}
	
	@Override
	protected Pair<List<Expression>, List<Expression>> getSubstPredicatesPair(
			StateExpression fromState, StateExpression toState) {
		return Pair.of(Collections.<Expression>emptyList(), Collections.<Expression>emptyList());
	}

	@Override
	protected SingleStateExpression doSubstitute(StateExpression state,
			final Collection<Expression> fromElems, 
			final Collection<Expression> toElems,
			Collection<Expression> fromPredicates, 
			Collection<Expression> toPredicates) {
		Preconditions.checkArgument(state.isSingle());
		
		if(fromElems.isEmpty())		return state.asSingle();
		
		SingleStateExpression singleState = state.asSingle();
		/* Substitute state elements */
		Iterable<Expression> newElems = Iterables.transform(singleState.getElements(), 
				new Function<Expression, Expression>() {
    	@Override
    	public Expression apply(Expression elem) {
    		return elem.subst(fromElems, toElems);
    	}
    });
    
    SingleStateExpression singleStatePrime = SingleStateExpression.create(
    		singleState.getName(), newElems);
    
    /* Copy properties */
    singleStatePrime.setProperties(singleState.getProperties());
    
    /* Substitute constraint */
    if(singleState.hasConstraint()) {
    	Expression pc = singleState.getConstraint();
    	BooleanExpression pcPrime = pc.subst(fromElems, toElems).asBooleanExpression();
    	singleStatePrime.setConstraint(pcPrime);
    }
    
    /* Substitute guards */
    if(singleState.hasGuard()) {
    	Expression guard = singleState.getGuard();
    	BooleanExpression guardPrime = guard.subst(fromElems, toElems).asBooleanExpression();
    	singleStatePrime.setGuard(guardPrime);
    }
    
    return singleStatePrime;
	}

	@Override
	protected SingleStateExpression joinPreStates(Iterable<StateExpression> preStates,
			Iterable<BooleanExpression> preGuards) {
	  Preconditions.checkArgument(Iterables.size(preStates) == Iterables.size(preGuards));
	  
	  ExpressionEncoding encoding = getExpressionEncoding();	  
	  
	  int preStatesSize = Iterables.size(preStates);
	  
	  SingleStateExpression firstPreState = preStates.iterator().next().asSingle();
	  int elemSize = firstPreState.getElements().size();
	  
	  List<Expression> joinStateElems = Lists.newArrayListWithCapacity(elemSize);
	  for(int idx = 0; idx < elemSize; idx++) {
	  	Collection<Expression> elemsAtIdx = Lists.newArrayListWithCapacity(preStatesSize);
	  	for(StateExpression preState : preStates) {
	  		elemsAtIdx.add(preState.asSingle().getElement(idx));
	  	}
	  	
	  	Expression joinElem = getITEExpression(encoding, elemsAtIdx, preGuards);
	  	joinStateElems.add(joinElem);
	  }
	
	  final String preStateName = firstPreState.getName();
	  
	  assert(Iterables.all(preStates, new Predicate<StateExpression>(){
			@Override
	    public boolean apply(StateExpression state) {
	      return state.asSingle().getName().equals(preStateName);
	    }
	  }));
	  
	  return SingleStateExpression.create(preStateName, joinStateElems);
	}
	
	void copyProperties(SingleStateExpression fromState, SingleStateExpression toState) {	
		toState.setProperties(fromState.getProperties());
		if(fromState.hasConstraint()) 
			toState.setConstraint(fromState.getConstraint());
		if(fromState.hasGuard()) 
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
	  Expression sizeVar = exprManager.variable(DEFAULT_SIZE_VARIABLE_NAME + 
	  		Identifiers.UNDERLINE + labelName, 
	      formatter.getSizeArrayType(), false);
		Expression constSizeArr = getConstSizeArr(formatter.getSizeArrayType());
		return Pair.of(sizeVar, constSizeArr);
	}
	
	SingleStateExpression freshSingleState(String labelName, xtc.type.Type type) {
		Preconditions.checkNotNull(type);
	  ExpressionManager exprManager = getExpressionManager();
	  IRDataFormatter formatter = getDataFormatter();
	  Expression memVar = exprManager.variable(DEFAULT_MEMORY_VARIABLE_NAME + 
	  		Identifiers.UNDERLINE + labelName, 
	  		exprManager.arrayType(formatter.getAddressType(), 
	  				formatter.getArrayElemType(type)), false);
	  Expression sizeVar = exprManager.variable(DEFAULT_SIZE_VARIABLE_NAME + 
	  		Identifiers.UNDERLINE + labelName, 
	      formatter.getSizeArrayType(), false);
	  return SingleStateExpression.create(labelName, memVar, sizeVar);
	}
	
	SingleStateExpression freshSingleState(String labelName, Type[] elemTypes) {
		Preconditions.checkArgument(elemTypes.length == 2);
	  ExpressionManager exprManager = getExpressionManager();
	  Expression memVar = exprManager.variable(DEFAULT_MEMORY_VARIABLE_NAME + 
	  		Identifiers.UNDERLINE + labelName, elemTypes[0], false);
	  Expression sizeVar = exprManager.variable(DEFAULT_SIZE_VARIABLE_NAME + 
	  		Identifiers.UNDERLINE + labelName, elemTypes[1], false);
	  return SingleStateExpression.create(labelName, memVar, sizeVar);
	}
	
	private SingleStateExpression substitute(StateExpression state, 
			final StateExpression stateVar, final StateExpression stateArg) {
		
		Pair<List<Expression>, List<Expression>> substElemsPair = 
				getSubstElemsPair(stateVar, stateArg);
		Pair<List<Expression>, List<Expression>> substPredsPair =
				getSubstPredicatesPair(state, stateArg);
		
		SingleStateExpression statePrime = doSubstitute(state, 
				substElemsPair.fst(),
				substElemsPair.snd(), 
				substPredsPair.fst(), 
				substPredsPair.snd());
	  
	  return statePrime;
	}

	private ArrayExpression getConstSizeArr(ArrayType sizeArrType) {
		ExpressionManager exprManager = getExpressionManager();
		IRDataFormatter formatter = getDataFormatter();
		
		if(Preferences.PROVER_Z3.equals(exprManager.getTheoremProver().getProviderName())) {
			return exprManager.storeAll(formatter.getSizeZero(), sizeArrType);
		}
		
		ArrayExpression sizeVar = exprManager.variable(ConstArray, sizeArrType, true).asArray();
		Expression indexVar = exprManager.boundVar(IndexVar, sizeArrType.getIndexType(), false);
		BooleanExpression axiom = exprManager.forall(indexVar, 
				sizeVar.index(indexVar).eq(
						exprManager.bitVectorZero(sizeArrType.getElementType().asBitVectorType().getSize())));
		getExpressionEncoding().addAssumption(axiom);
		return sizeVar;
	}
}

