package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import com.google.common.collect.Table;
import com.google.common.collect.Table.Cell;
import com.google.inject.Inject;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.safety.IRMemSafetyEncoding;
import edu.nyu.cascade.ir.state.SingleLambdaStateExpression.LabelType;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Pair;

public class MultiLambdaStateFactory<T> extends AbstractStateFactory<T> {

	private final SingleLambdaStateFactory<T> singleStateFactory;
	private final IRMemSafetyEncoding memSafetyEncoding;
	private PreProcessor<T> labelAnalyzer;
	
  @Inject
	MultiLambdaStateFactory(ExpressionEncoding encoding, IRDataFormatter formatter,
      IRMemSafetyEncoding memSafetyEncoding) {
	  super(encoding, formatter);
	  singleStateFactory = createSingleLambda(encoding, formatter, memSafetyEncoding);
	  this.memSafetyEncoding = memSafetyEncoding;
  }
	
	@Override
	public MultiLambdaStateExpression freshState() {
	  return MultiLambdaStateExpression.create();
	}
	
	@Override
	public MultiLambdaStateExpression addStackVar(StateExpression state, Expression lval, IRVarInfo info) {
		Preconditions.checkNotNull(lval.getNode());
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
		labelAnalyzer.addStackVar(lval);
		
		xtc.type.Type lvalType = info.getXtcType().resolve();
		T rep;
		
		if(lvalType.isArray() || lvalType.isStruct() || lvalType.isStruct()) {
	  	rep = labelAnalyzer.getPointsToRep(lval.getNode());
		} else {
			rep = labelAnalyzer.getRep(lval.getNode());
		}
		
		MultiLambdaStateExpression multiState = state.asMultiLambda();
		
		updateStateWithRep(multiState, rep);
		
		String label = labelAnalyzer.getRepId(rep);
		SingleLambdaStateExpression singleState = multiState.getStateMap().get(label);
		
		long size = CType.getSizeofType(lvalType);
		Expression sizeExpr = getExpressionEncoding().integerConstant(size);
		singleStateFactory.addStackVar(singleState, lval, sizeExpr);
		
		return multiState;
	}

	@Override
	public Expression eval(Expression expr, StateExpression stateVar,
	    StateExpression state) {	
		Pair<List<Expression>, List<Expression>> substElemsPair = 
				getSubstElemsPair(stateVar, state);
		Pair<List<Expression>, List<Expression>> substPredsPair = 
				getSubstPredicatesPair(stateVar, state);
		
		Collection<Expression> fromExprs = Lists.newArrayList();
	  fromExprs.addAll(substElemsPair.fst());
	  fromExprs.addAll(substPredsPair.fst());
	  
		Collection<Expression> toExprs = Lists.newArrayList();
		toExprs.addAll(substElemsPair.snd());
		toExprs.addAll(substPredsPair.snd());
		
		if(fromExprs.isEmpty()) return expr;
		
		return expr.subst(fromExprs, toExprs);
	}

	@Override
	public MultiLambdaStateExpression resolvePhiNode(Collection<StateExpression> preStates) {
		/* Build the joined state */
		MultiLambdaStateExpression resState = joinPreStates(preStates, null);
  	
		/* Set the constraint and guard */
		BooleanExpression joinConstraint = joinConstraints(preStates);
		resState.setConstraint(joinConstraint);
		BooleanExpression joinGuard = joinGuards(preStates);
		resState.setGuard(joinGuard);
		return resState;
	}

	@Override
	public Expression applyValidMalloc(StateExpression state, Expression ptr, Expression size) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		Preconditions.checkNotNull(ptr.getNode());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptr.getNode());
		T srcRep = labelAnalyzer.getSrcRep(ptrRep);
		
		MultiLambdaStateExpression multiState = state.asMultiLambda();
		
		updateStateWithRep(multiState, srcRep);
		
		String label = labelAnalyzer.getRepId(srcRep);
		SingleLambdaStateExpression singleState = multiState.getStateMap().get(label);
		
	  return singleStateFactory.applyValidMalloc(singleState, ptr, size);
	}

	@Override
	public BooleanExpression applyValidFree(StateExpression state, Expression ptr) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		Preconditions.checkNotNull(ptr.getNode());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptr.getNode());
		T srcRep = labelAnalyzer.getSrcRep(ptrRep);
		
		MultiLambdaStateExpression multiState = state.asMultiLambda();
		
		updateStateWithRep(multiState, srcRep);
		
		String label = labelAnalyzer.getRepId(srcRep);
		SingleLambdaStateExpression singleState = multiState.getStateMap().get(label);
		
		return singleStateFactory.applyValidFree(singleState, ptr);
	}

	@Override
	public Expression validAccess(StateExpression state, Expression ptr) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		Preconditions.checkNotNull(ptr.getNode());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptr.getNode());
		T srcRep = labelAnalyzer.getSrcRep(ptrRep);
		
		MultiLambdaStateExpression multiState = state.asMultiLambda();
		
		updateStateWithRep(multiState, srcRep);
		
		String label = labelAnalyzer.getRepId(srcRep);
		SingleLambdaStateExpression singleState = multiState.getStateMap().get(label);
		
		return singleStateFactory.validAccess(singleState, ptr);
	}

	@Override
	public Expression validAccessRange(StateExpression state, Expression ptr,
	    Expression size) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		Preconditions.checkNotNull(ptr.getNode());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptr.getNode());
		T srcRep = labelAnalyzer.getSrcRep(ptrRep);
		
		MultiLambdaStateExpression multiState = state.asMultiLambda();
		
		updateStateWithRep(multiState, srcRep);
		
		String label = labelAnalyzer.getRepId(srcRep);
		SingleLambdaStateExpression singleState = multiState.getStateMap().get(label);
		
		return singleStateFactory.validAccessRange(singleState, ptr, size);
	}

	@Override
	public BooleanExpression getDisjointAssumption(StateExpression state) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
		Map<String, SingleLambdaStateExpression> stateMap = state.asMultiLambda().getStateMap();
		Collection<BooleanExpression> preDisjoints = Lists.newArrayListWithCapacity(stateMap.size());
		
		for(SingleLambdaStateExpression subState : stateMap.values()) {
			preDisjoints.add(singleStateFactory.getDisjointAssumption(subState));
		}
		
		return getExpressionManager().and(preDisjoints);		
	}
	
	/** The new information may be:
	 * 1) the fresh sub-states generated during visiting expressions
	 * 2) the fresh labels generated during visiting safety-related functions
	 */
	@Override
	public void propagateNewInfo(StateExpression fromState, StateExpression toState) {
	  Preconditions.checkArgument(fromState.isMultiple() && fromState.isLambda());
	  Preconditions.checkArgument(toState.isMultiple() && toState.isLambda());
		
		propagateNewSubState(fromState, toState);
		
		/* Collection substitution state elements and predicates */
		Pair<List<Expression>, List<Expression>> substElemsPair = 
				getSubstElemsPair(fromState, toState);
		Pair<List<Expression>, List<Expression>> substPredsPair = 
				getSubstPredicatesPair(fromState, toState);
		
		Collection<Expression> fromExprs = Lists.newArrayList();
	  fromExprs.addAll(substElemsPair.fst());
	  fromExprs.addAll(substPredsPair.fst());
	  
		Collection<Expression> toExprs = Lists.newArrayList();
		toExprs.addAll(substElemsPair.snd());
		toExprs.addAll(substPredsPair.snd());
	  
		doPropagateNewInfo(fromState, toState, fromExprs, toExprs);
	}
	
	@Override
	public StateExpression alloc(StateExpression state, Expression ptr,
	    Expression size) {
		Expression region = createFreshRegion(ptr);
		MultiLambdaStateExpression statePrime = updateMemState(state, ptr, region);
		MultiLambdaStateExpression statePrime2 = updateSizeStateWithAlloc(statePrime, ptr, region, size);
  	return statePrime2;
	}

	@Override
  public MultiLambdaStateExpression updateMemState(StateExpression state,
      Expression memIdx, Expression memVal) {
		Preconditions.checkNotNull(memIdx.getNode());
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
		MultiLambdaStateExpression statePrime = state.copy().asMultiLambda();
		Map<String, SingleLambdaStateExpression> statePrimeMap = statePrime.getStateMap();

		T rep = labelAnalyzer.getRep(memIdx.getNode());
		String label = labelAnalyzer.getRepId(rep);
		updateStateWithRep(statePrime, rep);
		
		SingleLambdaStateExpression singleState = statePrimeMap.get(label);
		SingleLambdaStateExpression singleStatePrime = singleStateFactory.updateMemState(singleState, memIdx, memVal);
		statePrimeMap.put(label, singleStatePrime);
		
	  return statePrime;
  }

	@Override
  public MultiLambdaStateExpression updateSizeState(StateExpression state,
      Expression sizeIdx, Expression sizeVal) {
		Preconditions.checkNotNull(sizeIdx.getNode());
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
		MultiLambdaStateExpression statePrime = state.copy().asMultiLambda();
		Map<String, SingleLambdaStateExpression> statePrimeMap = statePrime.getStateMap();
		
		T ptrRep = labelAnalyzer.getPointsToRep(sizeIdx.getNode());
		String regLabel = labelAnalyzer.getRepId(ptrRep);
		updateStateWithRep(statePrime, ptrRep);
		
		SingleLambdaStateExpression singleState = statePrimeMap.get(regLabel);
		SingleLambdaStateExpression singleStatePrime = singleStateFactory
	  		.updateSizeState(singleState, sizeIdx, sizeVal);
		
		statePrimeMap.put(regLabel, singleStatePrime);
		
		return statePrime;
  }

	@Override
  public Expression deref(StateExpression state, Expression index) {
		Preconditions.checkNotNull(index.getNode());
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
		T rep = labelAnalyzer.getRep(index.getNode());
		String regLabel = labelAnalyzer.getRepId(rep);
		
		updateStateWithRep(state.asMultiLambda(), rep);
		
		SingleLambdaStateExpression singleState = state.asMultiLambda().getStateMap().get(regLabel);
		
		return singleStateFactory.deref(singleState, index);
  }
	
	@Override
  public Expression cleanup(StateExpression state, Expression expr) {
  	Preconditions.checkArgument(state.isMultiple() && state.isLambda());
  	Map<String, SingleLambdaStateExpression> stateMap = state.asMultiLambda().getStateMap();
		
  	Collection<Expression> fromExprs, toExprs;
  	fromExprs = Lists.newArrayList();
  	toExprs = Lists.newArrayList();
  	
		for(SingleLambdaStateExpression singleState : stateMap.values()) {
			Pair<Collection<Expression>, Collection<Expression>> pair = 
					singleStateFactory.getCleanupSubstPair(singleState);
			fromExprs.addAll(pair.fst());
			toExprs.addAll(pair.snd());
		}
		
		 boolean changed = false;
		 do {
			 Expression exprPrime = expr.subst(fromExprs, toExprs);
			 changed = exprPrime.equals(expr);
			 expr = exprPrime;
		 } while(!changed);
		 return expr;
  }

	@SuppressWarnings("unchecked")
	@Override
	public <X> void setLabelAnalyzer(PreProcessor<X> preprocessor) {
		labelAnalyzer = (PreProcessor<T>) preprocessor;
	}
	
	@Override
	public StateExpression scopeOptimize(StateExpression preState, 
			StateExpression postState) {
		return postState;
	}
	
	@Override
	public StateExpression propagateState(StateExpression cleanState,
	    StateExpression stateVar, StateExpression stateArg) {
	 StateExpression statePrime = refreshDuplicateLabels(stateArg, cleanState);
	 statePrime = substitute(statePrime, stateArg);
	 propagateProperties(stateArg, statePrime);
	 propagateNewSubState(stateArg, statePrime);
	 return statePrime;
	}
	
	@Override
	protected void propagateProperties(StateExpression fromState,
	    StateExpression toState) {
		Preconditions.checkArgument(fromState.isMultiple() && fromState.isLambda());
		Preconditions.checkArgument(toState.isMultiple() && toState.isLambda());
		
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
	  
	  Map<String, SingleLambdaStateExpression> fromStateMap = fromState.asMultiLambda().getStateMap();
	  Map<String, SingleLambdaStateExpression> toStateMap = toState.asMultiLambda().getStateMap();
	  	
	  Collection<String> commonNames = Sets.intersection(fromStateMap.keySet(), toStateMap.keySet());
	  if(commonNames.isEmpty()) return;
	  
	  for(String subStateName : commonNames) {
	  	SingleLambdaStateExpression fromSubState = fromStateMap.get(subStateName);
	  	SingleLambdaStateExpression toSubState = toStateMap.get(subStateName);
	  	singleStateFactory.propagateProperties(fromSubState, toSubState);
	  }
	}

	@Override
	protected MultiLambdaStateExpression updateSizeStateWithAlloc(
			StateExpression state, 
			Expression ptr, 
			Expression region, 
			Expression size) {
		Preconditions.checkArgument(state.isMultiple() || state.isLambda());
		Preconditions.checkNotNull(ptr.getNode());
		
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
		Map<String, SingleLambdaStateExpression> statePrimeMap = multiLambdaState.getStateMap();
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptr.getNode());
		String label = labelAnalyzer.getRepId(ptrRep);
		updateStateWithRep(multiLambdaState, ptrRep);
		
		labelAnalyzer.addAllocRegion(ptrRep, region);
		
		SingleLambdaStateExpression singleState2 = statePrimeMap.get(label);
		SingleLambdaStateExpression singleStatePrime2 = singleStateFactory
				.updateSizeStateWithAlloc(singleState2, ptr, region, size);
		statePrimeMap.put(label, singleStatePrime2);
  	return multiLambdaState;
	}
  
  @Override
	protected Pair<List<Expression>, List<Expression>> getSubstElemsPair(
			StateExpression fromState, StateExpression toState, boolean fetchFreshMap) {
		Preconditions.checkArgument(fromState.isMultiple() && fromState.isLambda());
		Preconditions.checkArgument(toState.isMultiple() && toState.isLambda());
		
		Map<String, SingleLambdaStateExpression> fromMap = fetchFreshMap ? 
				fromState.asMultiLambda().getFreshStateMap() : fromState.asMultiLambda().getStateMap();
		Map<String, SingleLambdaStateExpression> toMap = toState.asMultiLambda().getStateMap();
	  Collection<String> commonNames = Sets.intersection(toMap.keySet(), fromMap.keySet());
	  
	  if(commonNames.isEmpty())
	  	return Pair.of(Collections.<Expression>emptyList(), Collections.<Expression>emptyList());
	  
	  List<Expression> fromExprs = Lists.newArrayList();
	  List<Expression> toExprs = Lists.newArrayList();
	  
		for(String label : commonNames) {			
			/* Get substitution pair of size array and memory elements */
			Pair<List<Expression>, List<Expression>> sustElemsPair = 
					singleStateFactory.getSubstElemsPair(fromMap.get(label), toMap.get(label));
			
			fromExprs.addAll(sustElemsPair.fst());
			toExprs.addAll(sustElemsPair.snd());
		}
		return Pair.of(fromExprs, toExprs);
	}

	@Override
	protected Pair<List<Expression>, List<Expression>> getSubstPredicatesPair(
			StateExpression fromState, StateExpression toState) {
		Preconditions.checkArgument(fromState.isMultiple() && fromState.isLambda());
		Preconditions.checkArgument(toState.isMultiple() && toState.isLambda());
		
		Map<String, SingleLambdaStateExpression> fromMap = fromState.asMultiLambda().getStateMap();
		Map<String, SingleLambdaStateExpression> toMap = toState.asMultiLambda().getStateMap();
	  Collection<String> commonNames = Sets.intersection(toMap.keySet(), fromMap.keySet());
	  
	  if(commonNames.isEmpty()) {
	  	return Pair.of(Collections.<Expression>emptyList(), 
	  			Collections.<Expression>emptyList());
	  }
	  
	  List<Expression> fromExprs = Lists.newArrayList();
	  List<Expression> toExprs = Lists.newArrayList();
	  
		for(String label : commonNames) {
			/* Get substitution pair of memory safety predicate */
			Pair<List<Expression>, List<Expression>> statePredicatesPair = 
					singleStateFactory.getSubstPredicatesPair(
							fromMap.get(label), 
							toMap.get(label));
			
			fromExprs.addAll(statePredicatesPair.fst());
			toExprs.addAll(statePredicatesPair.snd());
		}
		return Pair.of(fromExprs, toExprs);
	}

	@Override
	protected MultiLambdaStateExpression doSubstitute(StateExpression state,
			final Collection<Expression> fromElems,
			final Collection<Expression> toElems,
			Collection<Expression> fromPredicates, 
			Collection<Expression> toPredicates) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
		if(fromElems.isEmpty() && fromPredicates.isEmpty()) return state.asMultiLambda();
		
		MultiLambdaStateExpression statePrime = state.asMultiLambda();
		
		if(!fromElems.isEmpty()) {
			
			/* Replace fromElems to toElems for every sub-state */
			Map<String, SingleLambdaStateExpression> stateMap = state.asMultiLambda().getStateMap();
			Map<String, SingleLambdaStateExpression> freshStateMap = state.asMultiLambda().getFreshStateMap();	
			
			Map<String, SingleLambdaStateExpression> statePrimeMap = Maps.newHashMap(stateMap);
			Map<String, SingleLambdaStateExpression> freshStatePrimeMap = Maps.newHashMap(freshStateMap);
			
			for(String name : stateMap.keySet()) {
				SingleLambdaStateExpression singleState = statePrimeMap.get(name);
				
				 /* Substitute state elements */
		    Iterable<Expression> newElems = Iterables.transform(singleState.getElements(), 
		    		new Function<Expression, Expression>() {
		    	@Override
		    	public Expression apply(Expression elem) {
		    		return elem.subst(fromElems, toElems);
		    	}
		    });
		    
		    SingleLambdaStateExpression singleStatePrime = singleStateFactory
		    		.createSingleLambdaState(singleState.getName(), newElems);
		    
		    /* Copy properties */
	    	singleStatePrime.setProperties(singleState.getProperties());
	    	
		    /* Copy safety-related properties */
	    	singleStatePrime.putAllPredicateMap(singleState.getPredicateMap());
	    	singleStatePrime.putAllSafetyPredicateClosures(singleState.getSafetyPredicateClosures());
	    	singleStatePrime.putAllSafetyPredicates(singleState.getSafetyPredicates());
		    
		    /* Substitute label table */
		    Table<VariableExpression, LabelType, Expression> labelTable = singleState.getLabelTable();
		    if(!labelTable.isEmpty()) {
		    	Table<VariableExpression, LabelType, Expression> labelMapPrime = HashBasedTable.create();
		    	for(Cell<VariableExpression, LabelType, Expression> cell : labelTable.cellSet()) {
		    		Expression value = cell.getValue();
		    		Expression valuePrime = value.subst(fromElems, toElems);
		    		labelMapPrime.put(cell.getRowKey(), cell.getColumnKey(), valuePrime);
		    	}
		    	singleStatePrime.putLabelTable(labelMapPrime);
		    }
				
				statePrimeMap.put(name, singleStatePrime);
			}
			
			statePrime = MultiLambdaStateExpression.create(freshStatePrimeMap, statePrimeMap);
			
			/* Copy properties */
	    statePrime.setProperties(state.getProperties());
		}
		
		Collection<Expression> fromExprs = Lists.newArrayList();
	  fromExprs.addAll(fromElems);
	  fromExprs.addAll(fromPredicates);
	  
		Collection<Expression> toExprs = Lists.newArrayList();
		toExprs.addAll(toElems);
		toExprs.addAll(toPredicates);
		
    /* Substitute constraint */
    if(state.hasConstraint()) {
    	BooleanExpression pc = state.getConstraint();
    	if(!fromExprs.isEmpty()) pc = pc.subst(fromExprs, toExprs).asBooleanExpression();
    	statePrime.setConstraint(pc);
    }
    
    /* Substitute guards */
    if(state.hasGuard()) {
    	BooleanExpression guard = state.getGuard();
    	if(!fromExprs.isEmpty())	guard = guard.subst(fromExprs, toExprs).asBooleanExpression();
    	statePrime.setGuard(guard);
    }
    
		return statePrime;
	}

	@Override
	protected MultiLambdaStateExpression joinPreStates(Iterable<StateExpression> preStates,
			Iterable<BooleanExpression> preGuards) {
		
		/* Initialize state map and fresh state map of result state */
		
		Multimap<String, Pair<StateExpression, BooleanExpression>> resFreshStateGuardMap = 
				HashMultimap.create();
		Multimap<String, Pair<StateExpression, BooleanExpression>> resStateGuardMap =
				HashMultimap.create();
		
		/* Build fresh state map and state map */
		
		for(StateExpression preState : preStates) {
			Map<String, SingleLambdaStateExpression> preStateMap = preState.asMultiLambda().getStateMap();
			
			for(Entry<String, SingleLambdaStateExpression> entry : preStateMap.entrySet()) {
				String elemName = entry.getKey();
				StateExpression preElemState = entry.getValue();
				resStateGuardMap.put(elemName, Pair.of(preElemState, preState.getGuard()));
			}
			
			Map<String, SingleLambdaStateExpression> preFreshStateMap = preState.asMultiLambda().getFreshStateMap();
			
			for(Entry<String, SingleLambdaStateExpression> entry : preFreshStateMap.entrySet()) {
				String elemName = entry.getKey();
				StateExpression preElemState = entry.getValue();
				resFreshStateGuardMap.put(elemName, Pair.of(preElemState, preState.getGuard()));
			}
		}
		
		/* Collect all names */
		Collection<String> elemNames = Sets.newHashSet();
		for(StateExpression preState : preStates) {
			elemNames.addAll(preState.asMultiLambda().getStateMap().keySet());
		}
		
		int preStateSize = Iterables.size(preStates);
		
		/* build res state map and res fresh state map */
		Map<String, SingleLambdaStateExpression> resStateMap = Maps.newHashMapWithExpectedSize(elemNames.size());
		Map<String, SingleLambdaStateExpression> resFreshStateMap = Maps.newHashMapWithExpectedSize(elemNames.size());
		
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
		  		Type[] elemTypes = preElemStates.get(0).asSingleLambda().getElemTypes();
		  		preElemStates.add(0, singleStateFactory.freshSingleLambdaState(elemName, elemTypes));
		  		preElemGuards.add(0, null); // this guard will be ignored in join pre-states
		  	}
				
				SingleLambdaStateExpression singleState = singleStateFactory.joinPreStates(
						preElemStates, preElemGuards);
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
		  		Type[] elemTypes = preElemStates.get(0).asSingleLambda().getElemTypes();
		  		preElemStates.add(0, singleStateFactory.freshSingleLambdaState(elemName, elemTypes));
		  		preElemGuards.add(0, null); // this guard will be ignored in join pre-states
		  	}
		  	
				SingleLambdaStateExpression singleState = singleStateFactory.joinPreStates(
						preElemStates, preElemGuards);
				resFreshStateMap.put(elemName, singleState);
			}
		}
		
		return MultiLambdaStateExpression.create(resFreshStateMap, resStateMap);
	}

	/**
	 * Find the duplicate labels between <code>fromState</code> and <code>toState</code>,
	 * generate fresh labels for them, and replace old labels to fresh labels in everything 
	 * may contains those labels. 
	 * 
	 * @param fromState
	 * @param toState
	 * @return a new state with same elements of <code>toState</code>, but with the fresh 
	 * labels substituted the duplicated labels.
	 */
	StateExpression refreshDuplicateLabels(StateExpression fromState,
	    StateExpression toState) {
		Preconditions.checkArgument(fromState.isMultiple() && fromState.isLambda());
		Preconditions.checkArgument(toState.isMultiple() && toState.isLambda());
		
		MultiLambdaStateExpression resState = toState.copy().asMultiLambda();
		
		/* Collect label replace pair and expression replace pair */
		
		Map<String, SingleLambdaStateExpression> fromStateMap = fromState.asMultiLambda().getStateMap();
		Map<String, SingleLambdaStateExpression> toStateMap = toState.asMultiLambda().getStateMap();
		
		Collection<String> commonSubStateNames = Sets.intersection(fromStateMap.keySet(), toStateMap.keySet());
		
		if(commonSubStateNames.isEmpty()) return resState;
		
		/* Store the single state name and its duplicated label pairs */
		Map<String, Pair<Collection<VariableExpression>, Collection<VariableExpression>>> subStateLabelPairMap = 
				Maps.newHashMapWithExpectedSize(commonSubStateNames.size());
		final Collection<Expression> fromExprs = Lists.newArrayList();
		final Collection<Expression> toExprs = Lists.newArrayList();
		
		for(String subStateName : commonSubStateNames) {
			SingleLambdaStateExpression fromSubState, toSubState;
			
			fromSubState = fromStateMap.get(subStateName);
			toSubState = toStateMap.get(subStateName);
			
			Table<VariableExpression, LabelType, Expression> fromLabelTable, toLabelTable;
			
			fromLabelTable = fromSubState.getLabelTable();
			toLabelTable = toSubState.getLabelTable();
			
			Collection<VariableExpression> duplicateLabels = Sets.intersection(
					toLabelTable.rowKeySet(), 
					fromLabelTable.rowKeySet());
			
			if(duplicateLabels.isEmpty()) continue;
			
			Pair<Pair<Collection<VariableExpression>, Collection<VariableExpression>>, 
					 Pair<Collection<Expression>, Collection<Expression>>> substLabelExprPairs = 
					 singleStateFactory.getSubstitutionLabelsExprs(toSubState, duplicateLabels);
			
			/* Store the substitution label pairs into subStateLabelPairMap */
			subStateLabelPairMap.put(subStateName, substLabelExprPairs.fst());
			
			/* Collect the substitution Expr pairs into fromExprs and toExprs */
			fromExprs.addAll(substLabelExprPairs.snd().fst());
			toExprs.addAll(substLabelExprPairs.snd().snd());
		}
		
		if(subStateLabelPairMap.isEmpty()) return resState;
		
		/* Update every sub-state */
		
		Map<String, SingleLambdaStateExpression> resStateMap = resState.getStateMap();
		
		for(String subStateName : toStateMap.keySet()) {
			SingleLambdaStateExpression toSubState = resStateMap.get(subStateName);
			
		  /* Update state elements */
		  Iterable<Expression> newElems = Iterables.transform(toSubState.getElements(), 
		  		new Function<Expression, Expression>() {
		  	@Override
		  	public Expression apply(Expression elem) {
		  		return elem.subst(fromExprs, toExprs);
		  	}
		  });
		  
		  /* Create a fresh single state */
			SingleLambdaStateExpression toSubStatePrime = singleStateFactory.createSingleLambdaState(
					toSubState.getName(), newElems);
			
			/* Copy properties */
			toSubStatePrime.setProperties(toSubState.getProperties());
			
			/* Copy safety predicate and predicate closure */
			toSubStatePrime.putAllSafetyPredicateClosures(toSubState.getSafetyPredicateClosures());
			toSubStatePrime.putAllSafetyPredicates(toSubState.getSafetyPredicates());
			
			/* Copy safety predicate map */
			toSubStatePrime.setPredicateMap(toSubState.getPredicateMap());
			
			/* Without duplicated labels, no need to update the label table */
			if(!subStateLabelPairMap.containsKey(subStateName)) {
				toSubStatePrime.putLabelTable(toSubState.getLabelTable());
				resStateMap.put(subStateName, toSubStatePrime);
				continue;
			}
			
			/* With duplicated labels and the label table should be updated */
			Pair<Collection<VariableExpression>, Collection<VariableExpression>> labelPair = 
					subStateLabelPairMap.get(subStateName);
			Collection<VariableExpression> fromLabels = labelPair.fst();
			Collection<VariableExpression> toLabels = labelPair.snd();
			
			/* Update label table */
			Table<VariableExpression, LabelType, Expression> labelTablePrime = 
					singleStateFactory.refreshLabelTable(
							toSubState.getLabelTable(), 
							fromLabels, toLabels, fromExprs, toExprs);
			
			toSubStatePrime.putLabelTable(labelTablePrime);
			
			/* Refresh duplicate labels in safety properties */
			memSafetyEncoding.refreshDuplicateLabels(
		  		toSubStatePrime, fromLabels, toLabels);
		
			resStateMap.put(subStateName, toSubStatePrime);  		
		}
		
		MultiLambdaStateExpression resStatePrime = MultiLambdaStateExpression.create(
				resState.getFreshStateMap(), resStateMap);
		
		/* Copy properties -- include constraint and guard */
		resStatePrime.setProperties(resState.getProperties());
		
		/* Constraint and guard may contain the old labels, needs to be updated */
		for(Pair<Collection<VariableExpression>, Collection<VariableExpression>> labelPair : subStateLabelPairMap.values()) {
			fromExprs.addAll(labelPair.fst()); 
			toExprs.addAll(labelPair.snd());
		}
		
	  /* Update constraint */
	  if(resState.hasConstraint()) {
	  	BooleanExpression pc = resState.getConstraint();
	  	BooleanExpression pcPrime = pc.subst(fromExprs, toExprs).asBooleanExpression();
	  	resStatePrime.setConstraint(pcPrime);
	  }
	  
	  /* Update guard */
	  if(resState.hasGuard()) {
	  	BooleanExpression guard = resState.getGuard();
	  	BooleanExpression guardPrime = guard.subst(fromExprs, toExprs).asBooleanExpression();
	  	resStatePrime.setGuard(guardPrime);
	  }
		
		return resStatePrime;
	}

	/**
	 * Propagate the labels in <code>fromState</code> which are not in the <code>
	 * toState</code> to the <code>toState</code>
	 * @param fromState
	 * @param toState
	 */
	void propagateNewSubState(StateExpression fromState, StateExpression toState) {
		Preconditions.checkArgument(fromState.isMultiple() && fromState.isLambda());
		Preconditions.checkArgument(toState.isMultiple() && toState.isLambda());
		
		Map<String, SingleLambdaStateExpression> fromMap, toMap;
		
		fromMap = fromState.asMultiLambda().getStateMap();
		toMap = toState.asMultiLambda().getStateMap();
		
		Collection<String> newSubStateNamesInFromState = Sets.newHashSet(fromMap.keySet());
		newSubStateNamesInFromState.removeAll(toMap.keySet());
		
		if(newSubStateNamesInFromState.isEmpty()) return;
		
		Map<String, SingleLambdaStateExpression> fromFreshMap, toFreshMap;
		
		fromFreshMap = fromState.asMultiLambda().getFreshStateMap();
		toFreshMap = toState.asMultiLambda().getFreshStateMap();
		
		for(String label : newSubStateNamesInFromState) {
			toMap.put(label, fromMap.get(label));
			toFreshMap.put(label, fromFreshMap.get(label));
		}
	}

	void doPropagateNewInfo(StateExpression fromState, StateExpression toState,
			Collection<Expression> fromExprs, Collection<Expression> toExprs) {
	  /* If the label is new, insert the new label and its state into both 
	   * state map and fresh state map; otherwise, update the label map in 
	   * the existing single state.
	   */
		Map<String, SingleLambdaStateExpression> fromMap, toMap;
		fromMap = fromState.asMultiLambda().getStateMap();
		toMap = toState.asMultiLambda().getStateMap();
		
		/* no the fresh labels needs to be added */
	  if(Sets.intersection(toMap.keySet(), fromMap.keySet()).isEmpty()) return;
		
		Map<String, SingleLambdaStateExpression> fromFreshMap, toFreshMap; 
		fromFreshMap = fromState.asMultiLambda().getFreshStateMap();
		toFreshMap = toState.asMultiLambda().getFreshStateMap();
		
		Set<String> commonNames = Sets.intersection(toMap.keySet(), fromMap.keySet());
	  for(String label : fromMap.keySet()) {
	  	if(commonNames.contains(label)) {
	  		SingleLambdaStateExpression singleFromState = fromMap.get(label);
	  		SingleLambdaStateExpression singleToState = toMap.get(label);
	  		Table<VariableExpression, LabelType, Expression> labelTable = 
	  				singleStateFactory.refreshLabelTable(
	  						singleFromState.getLabelTable(), fromExprs, toExprs);
	  		singleToState.putLabelTable(labelTable);
	  	} else {
	  		toFreshMap.put(label, fromFreshMap.get(label));
	  		toMap.put(label, fromMap.get(label));
	  	}
	  }
	}

	/** @param stateVar is useless here */
	private MultiLambdaStateExpression substitute(StateExpression state, StateExpression stateArg) {
		
		/* Collection substitution state elements and predicates */
		Pair<List<Expression>, List<Expression>> substElemsPair = 
				getSubstElemsPair(state, stateArg, true);
		Pair<List<Expression>, List<Expression>> substPredsPair = 
				getSubstPredicatesPair(state, stateArg);
		
		return doSubstitute(state, substElemsPair.fst(), substElemsPair.snd(),
				substPredsPair.fst(), substPredsPair.snd());
	}

	/**
   * Check an element state of <code>rep</code> is contained in <code>state</code>.
   * If not, add it to the state map, and thus update <code>state</code>
   * 
   * @param state
   * @param rep
   * @return <code>state</code> has been updated
   */
	private boolean updateStateWithRep(MultiLambdaStateExpression state, T rep) {
  	Map<String, SingleLambdaStateExpression> stateMap = state.getStateMap();
  	String label = labelAnalyzer.getRepId(rep);
  	
  	SingleLambdaStateExpression singleState;
	  if(stateMap.containsKey(label)) return false;
	  
	  xtc.type.Type ptrRepType = labelAnalyzer.getRepType(rep);
	  
	  Map<String, SingleLambdaStateExpression> freshStateMap = state.getFreshStateMap();
	  
	  singleState = singleStateFactory.freshSingleLambdaState(label, ptrRepType);
	  
	  freshStateMap.put(label, singleState);
	  stateMap.put(label, singleState);
	  
	  return false;
  }
}
