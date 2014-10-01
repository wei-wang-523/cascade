package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import com.google.inject.Inject;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.IRPartitionHeapEncoder;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Pair;

public class MultiStateFactory<T> extends AbstractStateFactory<T> {

	private final SingleStateFactory<T> singleStateFactory;
	private final IRPartitionHeapEncoder heapEncoder;
	
	private PreProcessor<T> labelAnalyzer;
	
  @Inject
	MultiStateFactory(ExpressionEncoding encoding, IRDataFormatter formatter, IRPartitionHeapEncoder parHeapEncoder) {
	  super(encoding, formatter);
	  singleStateFactory = createSingle(encoding, formatter);
	  heapEncoder = parHeapEncoder;
  }
	
	@SuppressWarnings("unchecked")
	@Override
	public <X> void setLabelAnalyzer(PreProcessor<X> preprocessor) {
		labelAnalyzer = (PreProcessor<T>) preprocessor;
	}
	
	@Override
	public MultiStateExpression freshState() {
	  return MultiStateExpression.create();
	}
	
	@Override
	public StateExpression addStackVar(StateExpression state, Expression lval, IRVarInfo info) {
		Preconditions.checkArgument(state.isMultiple());
		Preconditions.checkNotNull(lval.getNode());
		
		labelAnalyzer.addStackVar(lval);
		
		xtc.type.Type lvalType = info.getXtcType().resolve();
		T rep;
		
		if(lvalType.isArray() || lvalType.isStruct() || lvalType.isArray()) {
			/* The address should belongs to the group it points-to, where to reason
			 * about disjointness */
	  	rep = labelAnalyzer.getPointsToRep(lval.getNode());
		} else {
			rep = labelAnalyzer.getRep(lval.getNode());
		}
  	
		heapEncoder.addFreshAddress(labelAnalyzer.getRepId(rep), lval, info);
		
		updateStateWithRep(state.asMultiple(), rep);
		
		return state;
	}

	@Override
	public Expression eval(Expression expr, StateExpression stateVar,
	    StateExpression state) {
		Pair<List<Expression>, List<Expression>> substPair =
				getSubstElemsPair(stateVar, state);
		List<Expression> fromExprs = substPair.fst();
		List<Expression> toExprs = substPair.snd();
		
		if(fromExprs.isEmpty()) return expr;
		
		return expr.subst(fromExprs, toExprs);
	}

	@Override
	public StateExpression resolvePhiNode(Collection<StateExpression> preStates) {		
		/* Build the joined state */
		MultiStateExpression resState = joinPreStates(preStates, null);
  	
		/* Set the constraint and guard */
		BooleanExpression joinConstraint = joinConstraints(preStates);
		resState.setConstraint(joinConstraint);
		BooleanExpression joinGuard = joinGuards(preStates);
		resState.setGuard(joinGuard);
		return resState;
	}
	
  @Override
  public Expression cleanup(StateExpression state, Expression expr) {
  	Preconditions.checkArgument(state.isMultiple());
		Map<String, SingleStateExpression> stateMap = state.asMultiple().getStateMap();
		Collection<Expression> sizeVars = Lists.newArrayListWithCapacity(stateMap.size());
		Collection<Expression> sizeConsts = Lists.newArrayListWithCapacity(stateMap.size());
		for(SingleStateExpression subState : stateMap.values()) {
			Pair<Expression, Expression> pair = singleStateFactory.getCleanSizeSubstPair(subState);
			sizeVars.add(pair.fst());
			sizeConsts.add(pair.snd());
		}
		return expr.subst(sizeVars, sizeConsts);
  }

	@Override
	public Expression applyValidMalloc(StateExpression state, Expression ptr, Expression size) {
		Preconditions.checkArgument(state.isMultiple());
		Preconditions.checkNotNull(ptr.getNode());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptr.getNode());
		T srcRep = labelAnalyzer.getSrcRep(ptrRep);
		
		String srcRepId = labelAnalyzer.getRepId(srcRep);
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, srcRep);
		
    /* Get the related size array */
		SingleStateExpression singleState = multiState.getStateMap().get(srcRepId);
		ArrayExpression sizeArr = singleState.getElement(1).asArray();
		
    return heapEncoder.validMalloc(srcRepId, sizeArr, ptr, size);
	}

	@Override
	public BooleanExpression applyValidFree(StateExpression state, Expression ptr) {
		Preconditions.checkArgument(state.isMultiple());
		Preconditions.checkNotNull(ptr.getNode());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptr.getNode());
		T srcRep = labelAnalyzer.getSrcRep(ptrRep);
		
		String srcRepId = labelAnalyzer.getRepId(srcRep);
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, srcRep);
		
    /* Get the related size array */
		SingleStateExpression singleState = multiState.getStateMap().get(srcRepId);
		ArrayExpression sizeArr = singleState.getElement(1).asArray();
		
  	return heapEncoder.validFree(sizeArr, ptr);
	}

	@Override
	public Expression validAccess(StateExpression state, Expression ptr) {
		Preconditions.checkNotNull(ptr.getNode());
		Preconditions.checkArgument(state.isMultiple());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptr.getNode());
		T srcRep = labelAnalyzer.getSrcRep(ptrRep);
		
    String srcRepId = labelAnalyzer.getRepId(srcRep);
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, srcRep);
		
    /* Get the related size array */
		SingleStateExpression singleState = multiState.getStateMap().get(srcRepId);
		ArrayExpression sizeArr = singleState.getElement(1).asArray();
		
	  return getExpressionEncoding().or(heapEncoder.validMemAccess(srcRepId, sizeArr, ptr));
	}

	@Override
	public Expression validAccessRange(StateExpression state, Expression ptr,
	    Expression size) {
		Preconditions.checkNotNull(ptr.getNode());
		Preconditions.checkArgument(state.isMultiple());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptr.getNode());
		T srcRep = labelAnalyzer.getSrcRep(ptrRep);
		
    String srcRepId = labelAnalyzer.getRepId(srcRep);
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, srcRep);
		
    /* Get the related size array */
		SingleStateExpression singleState = multiState.getStateMap().get(srcRepId);
		ArrayExpression sizeArr = singleState.getElement(1).asArray();
		
	  return getExpressionEncoding().or(heapEncoder.validMemAccess(srcRepId, sizeArr, ptr, size));
	}

	@Override
	public Expression getDisjointAssumption(StateExpression state) {
		Preconditions.checkArgument(state.isMultiple());
		
		Map<String, SingleStateExpression> stateMap = state.asMultiple().getStateMap();
		
		Collection<Expression> preDisjoints = Lists.newArrayListWithCapacity(stateMap.size());
		
		for(Entry<String, SingleStateExpression> entry : stateMap.entrySet()) {
			String label = entry.getKey();
			SingleStateExpression subState = entry.getValue();
			ArrayExpression sizeArr = subState.getElement(1).asArray();
			preDisjoints.addAll(heapEncoder.disjointMemLayout(label, sizeArr));
		}
		
		return getExpressionManager().and(preDisjoints);		
	}
	
  /** The only new info is the fresh sub-states generated during visiting expressions
	 * like deference or function calls 
	 */
	@Override
	public void propagateNewInfo(StateExpression fromState, StateExpression toState) {
		propagateNewSubState(fromState, toState);
	}

	@Override
	public StateExpression alloc(StateExpression state, Expression ptr,
	    Expression size) {
		Expression region = createFreshRegion(ptr);
		MultiStateExpression statePrime = updateMemState(state, ptr, region);
		MultiStateExpression statePrime2 = updateSizeStateWithAlloc(statePrime, ptr, region, size);
  	return statePrime2;
	}

	@Override
  public MultiStateExpression updateMemState(StateExpression state,
      Expression memIdx, Expression memVal) {
		Preconditions.checkNotNull(memIdx.getNode());
		Preconditions.checkArgument(state.isMultiple());

		MultiStateExpression statePrime = state.copy().asMultiple();
		Map<String, SingleStateExpression> statePrimeMap = statePrime.getStateMap();
		
		T rep = labelAnalyzer.getRep(memIdx.getNode());
		String label = labelAnalyzer.getRepId(rep);
		updateStateWithRep(statePrime, rep);
		
		SingleStateExpression singleState = statePrimeMap.get(label);
		SingleStateExpression singleStatePrime = singleStateFactory
	  		.updateMemState(singleState, memIdx, memVal);
		
		statePrimeMap.put(label, singleStatePrime);
		
	  return statePrime;
  }

	@Override
  public MultiStateExpression updateSizeState(StateExpression state,
      Expression sizeIdx, Expression sizeVal) {
		Preconditions.checkNotNull(sizeIdx.getNode());
		Preconditions.checkArgument(state.isMultiple());
		
		MultiStateExpression statePrime = state.copy().asMultiple();
		
		T ptrRep = labelAnalyzer.getPointsToRep(sizeIdx.getNode());
		String regLabel = labelAnalyzer.getRepId(ptrRep);
		
		updateStateWithRep(statePrime, ptrRep);
		
		Map<String, SingleStateExpression> statePrimeMap = statePrime.getStateMap();
		
		SingleStateExpression singleState = statePrimeMap.get(regLabel);
		SingleStateExpression singleStatePrime = singleStateFactory
	  		.updateSizeState(singleState, sizeIdx, sizeVal);
		
		statePrimeMap.put(regLabel, singleStatePrime);
		
		return statePrime;
  }

	@Override
  public Expression deref(StateExpression state, Expression index) {
		Preconditions.checkNotNull(index.getNode());
		Preconditions.checkArgument(state.isMultiple());
		
		T rep = labelAnalyzer.getRep(index.getNode());
		String label = labelAnalyzer.getRepId(rep);
		
		updateStateWithRep(state.asMultiple(), rep);
		
		Map<String, SingleStateExpression> stateMap = state.asMultiple().getStateMap();
		
		SingleStateExpression singleState = stateMap.get(label);
		return singleStateFactory.deref(singleState, index);
  }
	
	@Override
	public StateExpression scopeOptimize(StateExpression preState, 
			StateExpression postState) {
		Preconditions.checkArgument(preState.isMultiple());
		Preconditions.checkArgument(postState.isMultiple());
		return postState;
	}
	
	@Override
	public StateExpression propagateState(StateExpression cleanState,
	    StateExpression stateVar, StateExpression stateArg) {
		 StateExpression statePrime = substitute(cleanState, stateArg);
		 propagateProperties(stateArg, statePrime);
		 propagateNewSubState(stateArg, statePrime);
		 return statePrime;
	}
	
  @Override
	protected void propagateProperties(StateExpression fromState,
	    StateExpression toState) {
		Preconditions.checkArgument(fromState.isMultiple());
		Preconditions.checkArgument(toState.isMultiple());
		
		/* Propagate fromState guard to toState */
	  if(fromState.hasGuard()) {
	  	BooleanExpression fromGuard = fromState.getGuard();
	  	toState.addGuard(fromGuard);
	  }
		
	  /* Propagate fromState constraint to toState */
	  if(fromState.hasConstraint()) {
	  	BooleanExpression fromConstraint = fromState.getConstraint();
	  	ExpressionManager exprManager = getExpressionManager();
	  	toState.addConstraint(fromConstraint, exprManager.tt(), exprManager.ff());
	  }
	}

	@Override
	protected MultiStateExpression updateSizeStateWithAlloc(StateExpression state,
	    Expression ptr, Expression region, Expression size) {
		Preconditions.checkNotNull(ptr.getNode());
		Preconditions.checkArgument(state.isMultiple());
		
  	MultiStateExpression multiState = state.asMultiple();
		Map<String, SingleStateExpression> statePrimeMap = multiState.getStateMap(); 
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptr.getNode());
		String label2 = labelAnalyzer.getRepId(ptrRep);
		updateStateWithRep(multiState, ptrRep);
		
		labelAnalyzer.addAllocRegion(ptrRep, region);
		
		SingleStateExpression singleState2 = statePrimeMap.get(label2);
		SingleStateExpression singleStatePrime2 = singleStateFactory.updateSizeState(singleState2, region, size);
		statePrimeMap.put(label2, singleStatePrime2);
		
		heapEncoder.addFreshRegion(label2, region);
		
  	return multiState;
	}

	@Override
	protected Pair<List<Expression>, List<Expression>> getSubstElemsPair(
			StateExpression fromState, StateExpression toState, boolean fetchFreshMap) {
		Preconditions.checkArgument(fromState.isMultiple());
		Preconditions.checkArgument(toState.isMultiple());
		
		Map<String, SingleStateExpression> fromMap = fetchFreshMap ? 
				fromState.asMultiple().getFreshStateMap() : fromState.asMultiple().getStateMap();
		Map<String, SingleStateExpression> toMap = toState.asMultiple().getStateMap();
	  Collection<String> commonNames = Sets.intersection(toMap.keySet(), fromMap.keySet());
	  
	  if(commonNames.isEmpty())
	  	return Pair.of(Collections.<Expression>emptyList(), Collections.<Expression>emptyList());
	  
	  List<Expression> fromExpr = Lists.newArrayList();
	  List<Expression> toExpr = Lists.newArrayList();
	  
		for(String label : commonNames) {
			/* Get substitution pair of size array and memory elements */
			Pair<List<Expression>, List<Expression>> sustElemsPair = 
					singleStateFactory.getSubstElemsPair(fromMap.get(label), toMap.get(label));
			
			fromExpr.addAll(sustElemsPair.fst());
			toExpr.addAll(sustElemsPair.snd());
		}
		
		return Pair.of(fromExpr, toExpr);
	}

	/** Return empty pair */
	@Override
	protected Pair<List<Expression>, List<Expression>> getSubstPredicatesPair(
			StateExpression fromState, StateExpression toState) {
		return Pair.of(Collections.<Expression>emptyList(), Collections.<Expression>emptyList());
	}

	@Override
	protected MultiStateExpression doSubstitute(StateExpression state,
			final Collection<Expression> fromElems, 
			final Collection<Expression> toElems,
			Collection<Expression> fromPredicates, 
			Collection<Expression> toPredicates) {
		Preconditions.checkArgument(state.isMultiple());
		
		if(fromElems.isEmpty()) return state.asMultiple();
		
		/* Substitution for every sub-state */
		Map<String, SingleStateExpression> stateMap = state.asMultiple().getStateMap();
		Map<String, SingleStateExpression> statePrimeMap = Maps.newHashMap(stateMap);
		
		for(String name : stateMap.keySet()) {
			SingleStateExpression singleState = statePrimeMap.get(name);
			
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
	    
	    singleStateFactory.copyProperties(singleState, singleStatePrime);
    	
			statePrimeMap.put(name, singleStatePrime);
		}
		
		Map<String, SingleStateExpression> freshStateMap = state.asMultiple().getFreshStateMap();
		Map<String, SingleStateExpression> freshStatePrimeMap = Maps.newHashMap(freshStateMap);
		MultiStateExpression statePrime = MultiStateExpression.create(freshStatePrimeMap, statePrimeMap);
		
		/* Copy properties */
		statePrime.setProperties(state.getProperties());
		
    /* Substitute constraint */
    if(state.hasConstraint()) {
    	BooleanExpression pc = state.getConstraint();
    	BooleanExpression pcPrime = pc.subst(fromElems, toElems).asBooleanExpression();
    	statePrime.setConstraint(pcPrime);
    }
    
    /* Substitute guards */
    if(state.hasGuard()) {
    	BooleanExpression guard = state.getGuard();
    	BooleanExpression guardPrime = guard.subst(fromElems, toElems).asBooleanExpression();
    	statePrime.setGuard(guardPrime);
    }
		
		return statePrime;
	}

	/** <code>preGuards</code> is useless for multi-state */
	@Override
	protected MultiStateExpression joinPreStates(Iterable<StateExpression> preStates,
			Iterable<BooleanExpression> preGuards) {
		
		/* Initialize state map and fresh state map of result state */
		
		Multimap<String, Pair<StateExpression, BooleanExpression>> resFreshStateGuardMap = 
				HashMultimap.create();
		Multimap<String, Pair<StateExpression, BooleanExpression>> resStateGuardMap =
				HashMultimap.create();
		
		/* Build fresh state map and state map */
		
		for(StateExpression preState : preStates) {
			BooleanExpression guard = preState.getGuard();
			
			Map<String, SingleStateExpression> preStateMap = preState.asMultiple().getStateMap();
			
			for(Entry<String, SingleStateExpression> entry : preStateMap.entrySet()) {
				String elemName = entry.getKey();
				StateExpression preElemState = entry.getValue();
				resStateGuardMap.put(elemName, Pair.of(preElemState, guard));
			}
			
			Map<String, SingleStateExpression> preFreshStateMap = preState.asMultiple().getFreshStateMap();
			
			for(Entry<String, SingleStateExpression> entry : preFreshStateMap.entrySet()) {
				String elemName = entry.getKey();
				StateExpression preElemState = entry.getValue();
				resFreshStateGuardMap.put(elemName, Pair.of(preElemState, guard));
			}
		}
		
		int preStateSize = Iterables.size(preStates);
		
		/* build res state map and res fresh state map */
		/* Collect all names */
		Collection<String> elemNames = Sets.newHashSet();
		
		for(StateExpression preState : preStates) {
			elemNames.addAll(preState.asMultiple().getStateMap().keySet());
		}
		
		Map<String, SingleStateExpression> resStateMap = Maps.newHashMapWithExpectedSize(elemNames.size());
		Map<String, SingleStateExpression> resFreshStateMap = Maps.newHashMapWithExpectedSize(elemNames.size());
		
		for(String elemName : elemNames) {
			
			{ /* build res state map */
				Collection<Pair<StateExpression, BooleanExpression>> preElemWithGuards = 
						resStateGuardMap.get(elemName);
				
		  	List<StateExpression> preElemStates = Lists.newArrayListWithCapacity(preStateSize);
		  	List<BooleanExpression> preElemGuards = Lists.newArrayListWithCapacity(preStateSize);
		  	
		  	for(Pair<StateExpression, BooleanExpression> pair : preElemWithGuards) {
		  		preElemStates.add(pair.fst()); preElemGuards.add(pair.snd());
		  	}
		  	
		  	if(preElemWithGuards.size() < preStateSize) { // set default case
		  		Type[] elemTypes = preElemStates.get(0).asSingle().getElemTypes();
		  		preElemStates.add(0, singleStateFactory.freshSingleState(elemName, elemTypes));
		  		preElemGuards.add(0, null); // this guard will be ignored in join pre-states
		  	}
				
				SingleStateExpression singleState = singleStateFactory.joinPreStates(preElemStates, preElemGuards);
				resStateMap.put(elemName, singleState);
			}
			
			{ /* build res fresh state map */
				Collection<Pair<StateExpression, BooleanExpression>> preElemWithGuards = 
						resFreshStateGuardMap.get(elemName);
				
		  	List<StateExpression> preElemStates = Lists.newArrayListWithCapacity(preStateSize);
		  	List<BooleanExpression> preElemGuards = Lists.newArrayListWithCapacity(preStateSize);
		  	
		  	for(Pair<StateExpression, BooleanExpression> pair : preElemWithGuards) {
		  		preElemStates.add(pair.fst()); preElemGuards.add(pair.snd());
		  	}
		  	
		  	if(preElemWithGuards.size() < preStateSize) { // set default case
		  		Type[] elemTypes = preElemStates.get(0).asSingle().getElemTypes();
		  		preElemStates.add(0, singleStateFactory.freshSingleState(elemName, elemTypes));
		  		preElemGuards.add(0, null); // this guard will be ignored in join pre-states
		  	}
				
				SingleStateExpression singleState = singleStateFactory.joinPreStates(preElemStates, preElemGuards);
				resFreshStateMap.put(elemName, singleState);
			}
		}
		
		/* build res multi-state with constraint and guard */
		
		return MultiStateExpression.create(resFreshStateMap, resStateMap);
	}

	/**
	 * Propagate the new labels in <code>fromState</code> which are not in the <code>
	 * toState</code> into the <code>toState</code>
	 * @param fromState
	 * @param toState
	 */
	void propagateNewSubState(StateExpression fromState, StateExpression toState) {
		Preconditions.checkArgument(fromState.isMultiple());
		Preconditions.checkArgument(toState.isMultiple());
		
		Map<String, SingleStateExpression> fromMap = fromState.asMultiple().getStateMap();
		Map<String, SingleStateExpression> toMap = toState.asMultiple().getStateMap();
		
		Collection<String> newSubStateNamesInFromState = Sets.newHashSet(fromMap.keySet());
		newSubStateNamesInFromState.removeAll(toMap.keySet());
		
		if(newSubStateNamesInFromState.isEmpty()) return;
		
		Map<String, SingleStateExpression> fromFreshMap = fromState.asMultiple().getFreshStateMap();
		Map<String, SingleStateExpression> toFreshMap = toState.asMultiple().getFreshStateMap();
		
		for(String label : newSubStateNamesInFromState) {
			toMap.put(label, fromMap.get(label));
			toFreshMap.put(label, fromFreshMap.get(label));
		}
	}

	private MultiStateExpression substitute(StateExpression state,
			StateExpression stateArg) {
		
		/* Collection substitution state elements and predicates */
		Pair<List<Expression>, List<Expression>> substElemsPair = 
				getSubstElemsPair(state, stateArg, true);
		Pair<List<Expression>, List<Expression>> substPredsPair =
				getSubstPredicatesPair(state, stateArg);
		
		MultiStateExpression statePrime = doSubstitute(state, 
				substElemsPair.fst(),
				substElemsPair.snd(), 
				substPredsPair.fst(), 
				substPredsPair.snd());
	  
	  return statePrime;
	}

	/**
   * Check an element state of <code>rep</code> is contained in <code>state</code>.
   * If not, add it to the state map, and thus update <code>state</code>
   * 
   * @param state
   * @param rep
   * @return <code>state</code> has been updated
   */
	private boolean updateStateWithRep(MultiStateExpression state, T rep) {
  	Map<String, SingleStateExpression> stateMap = state.getStateMap();
  	String label = labelAnalyzer.getRepId(rep);
  	
  	SingleStateExpression singleState;
	  if(stateMap.containsKey(label)) return false;
	  
	  xtc.type.Type ptrRepType = labelAnalyzer.getRepType(rep);
	  
	  Map<String, SingleStateExpression> freshStateMap = state.getFreshStateMap();
	  
	  singleState = singleStateFactory.freshSingleState(label, ptrRepType);
	  
	  freshStateMap.put(label, singleState);
	  stateMap.put(label, singleState);
	  
	  return false;
  }
}
