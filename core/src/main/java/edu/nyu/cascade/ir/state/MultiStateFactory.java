package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.annotation.Nullable;

import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import com.google.inject.Inject;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.IRPartitionHeapEncoder;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.ArrayType;
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
  
	@Override
	public void reset() {
		heapEncoder.reset();
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
	public void addStackVar(StateExpression state, Expression lval, IRVarInfo info) {
		Preconditions.checkArgument(state.isMultiple());
		
		xtc.type.Type lvalType = info.getXtcType().resolve();
		Node node = info.getDeclarationNode();
		
		labelAnalyzer.addStackVar(lval, node);
		
		T rep;
		
		if(lvalType.isArray() || lvalType.isStruct() || lvalType.isUnion()) {
			/* The address should belongs to the group it points-to, where to reason
			 * about disjointness */
	  	rep = labelAnalyzer.getPointsToRep(node);
		} else {
			rep = labelAnalyzer.getRep(node);
		}
  	
		heapEncoder.addFreshAddress(labelAnalyzer.getRepId(rep), lval, info);
		updateStateWithRep(state.asMultiple(), rep);
	}

	@Override
	public StateExpression resolvePhiNode(Collection<StateExpression> preStates) {
		/* Build the joined state */
  	Iterable<BooleanExpression> preGuards = Iterables.transform(preStates, pickGuard);
		MultiStateExpression joinState = joinPreStates(preStates, preGuards);
  	
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
  	Preconditions.checkArgument(state.isMultiple());
		Map<String, SingleStateExpression> stateMap = state.asMultiple().getStateMap();
		Collection<Expression> vars = Lists.newArrayListWithCapacity(stateMap.size());
		Collection<Expression> consts = Lists.newArrayListWithCapacity(stateMap.size());
		for(SingleStateExpression subState : stateMap.values()) {
			Pair<Expression, Expression> pair = singleStateFactory.getCleanSizeSubstPair(subState);
			vars.add(pair.fst());
			consts.add(pair.snd());
			
			pair = singleStateFactory.getCleanMarkSubstPair(subState);
			vars.add(pair.fst());
			consts.add(pair.snd());
		}
		Expression exprPrime = expr.subst(vars, consts);
		
		return exprPrime;
  }
  
	@Override
	public BooleanExpression applyMemset(StateExpression state, Expression region, 
			Expression size, Expression value, Node ptrNode) {
		Preconditions.checkArgument(state.isMultiple());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptrNode);
		T srcRep = labelAnalyzer.getSrcRep(ptrRep);
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, srcRep);
		
		String srcRepId = labelAnalyzer.getRepId(srcRep);
		SingleStateExpression singleState = multiState.getStateMap().get(srcRepId);
		
    return singleStateFactory.applyMemset(singleState, region, size, value, ptrNode);
	}
	
	@Override
	public BooleanExpression applyMemcpy(StateExpression state, Expression destRegion, 
			Expression srcRegion, Expression size, Node destNode, Node srcNode) {
		Preconditions.checkArgument(state.isMultiple());
		
		T destPtrRep = labelAnalyzer.getPointsToRep(destNode);
		T destRep = labelAnalyzer.getSrcRep(destPtrRep);
		
		T srcPtrRep = labelAnalyzer.getPointsToRep(srcNode);
		T srcRep = labelAnalyzer.getSrcRep(srcPtrRep);
		
		MultiStateExpression multiState = state.asMultiple();
		
		updateStateWithRep(multiState, destRep);
		updateStateWithRep(multiState, srcRep);
		
		String destLabel = labelAnalyzer.getRepId(destRep);
		String srcLabel = labelAnalyzer.getRepId(srcRep);
		SingleStateExpression destState = multiState.getStateMap().get(destLabel);
		SingleStateExpression srcState = multiState.getStateMap().get(srcLabel);
		
		ArrayExpression destMem = destState.getMemory();
		ArrayExpression srcMem = srcState.getMemory();
		
		IRDataFormatter formatter = getDataFormatter();
		return formatter.memoryCopy(destMem, srcMem, destRegion, srcRegion, size);
	}

	@Override
	public BooleanExpression applyValidMalloc(StateExpression state, Expression ptr, 
			Expression size, Node pNode) {
		Preconditions.checkArgument(state.isMultiple());
		
		T ptrRep = labelAnalyzer.getPointsToRep(pNode);
		T srcRep = labelAnalyzer.getSrcRep(ptrRep);
		
		String srcRepId = labelAnalyzer.getRepId(srcRep);
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, srcRep);
		
    /* Get the related size array */
		SingleStateExpression singleState = multiState.getStateMap().get(srcRepId);
		ArrayExpression sizeArr = singleState.getSize();
		
    return heapEncoder.validMalloc(srcRepId, sizeArr, ptr, size);
	}

	@Override
	public BooleanExpression applyValidFree(StateExpression state, Expression region, Node ptrNode) {
		Preconditions.checkArgument(state.isMultiple());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptrNode);
		T srcRep = labelAnalyzer.getSrcRep(ptrRep);
		
		String srcRepId = labelAnalyzer.getRepId(srcRep);
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, srcRep);
		
    /* Get the related size array */
		SingleStateExpression singleState = multiState.getStateMap().get(srcRepId);
		ArrayExpression markArr = singleState.getMark();
		
  	return heapEncoder.validFree(markArr, region);
	}

	@Override
	public BooleanExpression validAccess(StateExpression state, Expression ptr, Node ptrNode) {
		Preconditions.checkArgument(state.isMultiple());
		
		xtc.type.Type ptrType = CType.getType(ptrNode).resolve();
		T srcRep;
		
		if(ptrType.isArray() || ptrType.isStruct() || ptrType.isUnion()) {
			/* The address should belongs to the group it points-to, where to reason
			 * about disjointness */
			T ptrRep = labelAnalyzer.getPointsToRep(ptrNode);
			srcRep = labelAnalyzer.getSrcRep(ptrRep);
		} else {
			srcRep = labelAnalyzer.getRep(ptrNode);
			srcRep = labelAnalyzer.getSrcRep(srcRep);
		}
		
    String srcRepId = labelAnalyzer.getRepId(srcRep);
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, srcRep);
		
    /* Get the related size array */
		SingleStateExpression singleState = multiState.getStateMap().get(srcRepId);
		ArrayExpression sizeArr = singleState.getSize();
		
	  return getExpressionManager().or(heapEncoder.validMemAccess(srcRepId, sizeArr, ptr));
	}

	@Override
	public BooleanExpression validAccessRange(StateExpression state, Expression ptr,
	    Expression size, Node ptrNode) {
		Preconditions.checkArgument(state.isMultiple());
		
		xtc.type.Type ptrType = CType.getType(ptrNode).resolve();
		T srcRep;
		
		if(ptrType.isArray() || ptrType.isStruct() || ptrType.isUnion()) {
			/* The address should belongs to the group it points-to, where to reason
			 * about disjointness */
			T ptrRep = labelAnalyzer.getPointsToRep(ptrNode);
			srcRep = labelAnalyzer.getSrcRep(ptrRep);
		} else {
			srcRep = labelAnalyzer.getRep(ptrNode);
			srcRep = labelAnalyzer.getSrcRep(srcRep);
		}
		
    String srcRepId = labelAnalyzer.getRepId(srcRep);
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, srcRep);
		
    /* Get the related size array */
		SingleStateExpression singleState = multiState.getStateMap().get(srcRepId);
		ArrayExpression sizeArr = singleState.getSize();
		
	  return getExpressionManager().or(heapEncoder.validMemAccess(srcRepId, sizeArr, ptr, size));
	}

	@Override
	public BooleanExpression getDisjointAssumption(StateExpression state) {
		Preconditions.checkArgument(state.isMultiple());
		
		Map<String, SingleStateExpression> stateMap = state.asMultiple().getStateMap();
		
		Collection<Expression> preDisjoints = Lists.newArrayListWithCapacity(stateMap.size());
		
		for(Entry<String, SingleStateExpression> entry : stateMap.entrySet()) {
			String label = entry.getKey();
			SingleStateExpression subState = entry.getValue();
			ArrayExpression sizeArr = subState.getSize();
			preDisjoints.addAll(heapEncoder.disjointMemLayout(label, sizeArr));
		}
		
		return getExpressionManager().and(preDisjoints);		
	}

	@Override
	public void malloc(StateExpression state, Expression ptr,
	    Expression size, Node ptrNode) {
		ExpressionEncoding encoding = getExpressionEncoding();
		Expression region = createFreshRegion();
		BooleanExpression tt = encoding.tt().asBooleanExpression();
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
	public void alloca(StateExpression state, Expression ptr,
	    Expression size, Node ptrNode) {
		Expression region = createFreshRegion();
		updateMemState(state, ptr, ptrNode, region, null);
		updateSizeStateWithAlloc(state, ptr, region, size, ptrNode);
		state.addConstraint(applyValidMalloc(state, region, size, ptrNode));
	}
	
	@Override
	public void propagateState(StateExpression cleanState,
	    StateExpression stateVar, StateExpression stateArg) {
		substitute(cleanState, stateVar, stateArg);
		cleanState.addPreGuard(stateArg.getGuard());
		cleanState.addConstraint(stateArg.getConstraint());
		 
		propagateNewSubState(stateArg, cleanState);
	}
	
	@Override
	public void initializeDefault(StateExpression state, Expression lval,
			Node lNode) {
		Preconditions.checkArgument(state.isMultiple());
		
		xtc.type.Type idxType = CType.getType(lNode).resolve();
				
		T rep;
		
		if(idxType.isArray() || idxType.isStruct() || idxType.isUnion()) {
			/* The address should belongs to the group it points-to, where to reason
			 * about disjointness */
			T ptrRep = labelAnalyzer.getPointsToRep(lNode);
			rep = labelAnalyzer.getSrcRep(ptrRep);
		} else {
			rep = labelAnalyzer.getRep(lNode);
		}
		
		String label = labelAnalyzer.getRepId(rep);
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, rep);
		
		Map<String, SingleStateExpression> stateMap = multiState.getStateMap();
		SingleStateExpression singleState = stateMap.get(label);
		singleStateFactory.initializeDefault(singleState, lval, lNode);
	}
	
	@Override
	public void initializeValues(StateExpression state, Expression lval,
			Node lNode, List<Expression> rvals, List<Node> rNodes) {
		Preconditions.checkArgument(state.isMultiple());
		
		xtc.type.Type idxType = CType.getType(lNode).resolve();
		
		T rep;
		
		if(idxType.isArray() || idxType.isStruct() || idxType.isUnion()) {
			/* The address should belongs to the group it points-to, where to reason
			 * about disjointness */
			T ptrRep = labelAnalyzer.getPointsToRep(lNode);
			rep = labelAnalyzer.getSrcRep(ptrRep);
		} else {
			rep = labelAnalyzer.getRep(lNode);
		}
		
		String label = labelAnalyzer.getRepId(rep);
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, rep);
		
		Map<String, SingleStateExpression> stateMap = multiState.getStateMap();
		SingleStateExpression singleState = stateMap.get(label);
		singleStateFactory.initializeValues(singleState, lval, lNode, rvals, rNodes);
	}

	@Override
	public MultiStateExpression copy(StateExpression state) {
		Preconditions.checkArgument(state.isMultiple());
		MultiStateExpression multiState = state.asMultiple();
		
		Map<String, SingleStateExpression> stateMapCopy = Maps.newHashMap();
		
		for(Entry<String, SingleStateExpression> entry : multiState.getStateMap().entrySet()) {
			stateMapCopy.put(entry.getKey(), singleStateFactory.copy(entry.getValue()));
		}
		
		MultiStateExpression stateClone = MultiStateExpression.create(stateMapCopy);
		
		stateClone.setProperties(state.getProperties());
		stateClone.setConstraint(state.getConstraint());
		stateClone.setGuard(state.getGuard());
  	
		return stateClone;
	}
	
	@Override
	protected Expression getSizeOfRegion(StateExpression state, Expression region, Node ptrNode) {
		Preconditions.checkArgument(state.isMultiple());
		T ptrRep = labelAnalyzer.getPointsToRep(ptrNode);
		String label = labelAnalyzer.getRepId(ptrRep);
		
		Map<String, SingleStateExpression> stateMap = state.asMultiple().getStateMap();
		SingleStateExpression singleState = stateMap.get(label);
		
		ArrayExpression sizeArr = singleState.getSize();
		return getDataFormatter().indexSizeArray(sizeArr, region);
	}
	
  @Override
	protected void updateMemState(StateExpression state,
	    Expression index, Node idxNode, Expression value, @Nullable Node valNode) {
		Preconditions.checkArgument(state.isMultiple());
		
		xtc.type.Type idxType = CType.getType(idxNode).resolve();
		T rep;
		
		if(idxType.isArray() || idxType.isStruct() || idxType.isUnion()) {
			/* The address should belongs to the group it points-to, where to reason
			 * about disjointness */
			T ptrRep = labelAnalyzer.getPointsToRep(idxNode);
			rep = labelAnalyzer.getSrcRep(ptrRep);
		} else {
			rep = labelAnalyzer.getRep(idxNode);
		}
		
		String label = labelAnalyzer.getRepId(rep);
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, rep);
		
		Map<String, SingleStateExpression> stateMap = multiState.getStateMap();
		SingleStateExpression singleState = stateMap.get(label);
		singleStateFactory.updateMemState(singleState, index, idxNode, value, valNode);
	}

	@Override
	protected void updateSizeState(StateExpression state,
	    Expression region, Expression sizeVal, Node ptrNode) {
		Preconditions.checkArgument(state.isMultiple());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptrNode);
		String regLabel = labelAnalyzer.getRepId(ptrRep);
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, ptrRep);
		
		Map<String, SingleStateExpression> stateMap = multiState.getStateMap();
		SingleStateExpression singleState = stateMap.get(regLabel);
		singleStateFactory.updateSizeState(singleState, region, sizeVal, ptrNode);
	}
	
	@Override
	protected void updateMarkState(StateExpression state,
	    Expression region, BooleanExpression mark, Node ptrNode) {
		Preconditions.checkArgument(state.isMultiple());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptrNode);
		String regLabel = labelAnalyzer.getRepId(ptrRep);
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, ptrRep);
		
		Map<String, SingleStateExpression> stateMap = multiState.getStateMap();
		SingleStateExpression singleState = stateMap.get(regLabel);
		singleStateFactory.updateMarkState(singleState, region, mark, ptrNode);
	}

	@Override
	protected void updateSizeStateWithAlloc(StateExpression state,
	    Expression ptr, Expression region, Expression size, Node ptrNode) {
		Preconditions.checkArgument(state.isMultiple());
  	
		T ptrRep = labelAnalyzer.getPointsToRep(ptrNode);
		String label = labelAnalyzer.getRepId(ptrRep);
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, ptrRep);
		
		labelAnalyzer.addAllocRegion(ptrRep, region, ptrNode);
		
		Map<String, SingleStateExpression> statePrimeMap = multiState.getStateMap(); 
		
		SingleStateExpression singleState = statePrimeMap.get(label);
		singleStateFactory.updateSizeState(singleState, region, size, ptrNode);
		
		heapEncoder.addFreshRegion(label, region);
	}

	@Override
	protected void doSubstitute(StateExpression state,
			final Collection<Expression> fromElems, 
			final Collection<Expression> toElems,
			Collection<Expression> fromPredicates, 
			Collection<Expression> toPredicates) {
		Preconditions.checkArgument(state.isMultiple());
		
		if(fromElems.isEmpty()) return;
		
		/* Substitution for every sub-state */
		Map<String, SingleStateExpression> stateMap = state.asMultiple().getStateMap();
		
		for(String name : stateMap.keySet()) {
			SingleStateExpression singleState = stateMap.get(name);
			
			 /* Substitute state elements */
			Expression newMem = singleState.getMemory().subst(fromElems, toElems);
			Expression newSize = singleState.getSize().subst(fromElems, toElems);
			Expression newMark = singleState.getMark().subst(fromElems, toElems);
			singleState.setMemory(newMem.asArray());
			singleState.setSize(newSize.asArray());
			singleState.setMark(newMark.asArray());
		}
	  
	  if(state.getConstraint() != null) { /* Substitute constraint */
	  	BooleanExpression pc = state.getConstraint();
	  	BooleanExpression pcPrime = pc.subst(fromElems, toElems).asBooleanExpression();
	  	state.setConstraint(pcPrime);
	  }
	  
	  { /* Substitute guards */
	  	BooleanExpression guard = state.getGuard();
	  	BooleanExpression guardPrime = guard.subst(fromElems, toElems).asBooleanExpression();
	  	state.setGuard(guardPrime);
	  }
	}

	@Override
	protected void propagateProperties(StateExpression fromState,
	    StateExpression toState) {
	}

	@Override
	protected Pair<List<Expression>, List<Expression>> getSubstElemsPair(
			StateExpression fromState, StateExpression toState) {
		Preconditions.checkArgument(fromState.isMultiple());
		Preconditions.checkArgument(toState.isMultiple());
		
		Map<String, SingleStateExpression> fromMap = fromState.asMultiple().getStateMap();
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

	/** <code>preGuards</code> is useless for multi-state */
	@Override
	protected MultiStateExpression joinPreStates(Iterable<StateExpression> preStates,
			Iterable<BooleanExpression> preGuards) {
		
		/* Collect all names */
		Collection<String> elemNames = Sets.newHashSet();
		
		for(StateExpression preState : preStates) {
			elemNames.addAll(preState.asMultiple().getStateMap().keySet());
		}
		
		if(elemNames.isEmpty()) return MultiStateExpression.create();
		
		/* Initialize state map of result state */
		
		Multimap<String, Pair<StateExpression, BooleanExpression>> resStateGuardMap =
				LinkedHashMultimap.create();
		
		/* Build state map */
		Iterator<BooleanExpression> preGuardItr = preGuards.iterator();
		for(StateExpression preState : preStates) {
			BooleanExpression guard = preGuardItr.next();
			
			Map<String, SingleStateExpression> preStateMap = preState.asMultiple().getStateMap();
			
			for(Entry<String, SingleStateExpression> entry : preStateMap.entrySet()) {
				String elemName = entry.getKey();
				StateExpression preElemState = entry.getValue();
				resStateGuardMap.put(elemName, Pair.of(preElemState, guard));
			}
		}
		
		/* build res state map */
		
		int preStateSize = Iterables.size(preStates);
		
		Map<String, SingleStateExpression> resStateMap = Maps.newHashMapWithExpectedSize(elemNames.size());
		
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
		  		ArrayType[] elemTypes = preElemStates.get(0).asSingle().getElemTypes();
		  		preElemStates.add(0, freshSingleState(elemName, elemTypes));
		  		preElemGuards.add(0, null); // this guard will be ignored in join pre-states
		  	}
				
				SingleStateExpression singleState = singleStateFactory.joinPreStates(preElemStates, preElemGuards);
				resStateMap.put(elemName, singleState);
			}
		}
		
		/* build res multi-state with constraint and guard */
		
		return MultiStateExpression.create(resStateMap);
	}

	/**
	 * Substitute the <code>stateVar</code> in <code>state</code>
	 * with <code>stateArg</code>
	 * @param state
	 * @param stateVar
	 * @param stateArg
	 * @return
	 */
	@Override
	protected void substitute(StateExpression state, 
			StateExpression stateVar, StateExpression stateArg) {
		
		/* Collection substitution state elements and predicates */
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
		Preconditions.checkArgument(state.isMultiple());
		
		T rep = labelAnalyzer.getRep(indexNode);
		String label = labelAnalyzer.getRepId(rep);
		
		updateStateWithRep(state.asMultiple(), rep);
		
		Map<String, SingleStateExpression> stateMap = state.asMultiple().getStateMap();
		SingleStateExpression singleState = stateMap.get(label);
		xtc.type.Type indexType = CType.getType(indexNode);
		return getDataFormatter().indexMemoryArray(singleState.getMemory(), index, indexType);
	}

	@Override
	protected Expression eval(Expression expr, StateExpression stateVar,
	    StateExpression state) {
		Pair<List<Expression>, List<Expression>> substPair =
				getSubstElemsPair(stateVar, state);
		List<Expression> fromExprs = substPair.fst();
		List<Expression> toExprs = substPair.snd();
		
		Expression exprPrime = fromExprs.isEmpty() ? expr : expr.subst(fromExprs, toExprs);
		return exprPrime;
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
		
		for(String label : newSubStateNamesInFromState) {
			toMap.put(label, fromMap.get(label));
		}
	}

	/**
   * Check an element state of <code>rep</code> is contained in <code>multiState</code>.
   * If not, add it to the state map, and thus <code>multiState</code> get changed
   * 
   * @param multiState
   * @param rep
   * @return <code>state</code> has been updated
   */
	private boolean updateStateWithRep(MultiStateExpression multiState, T rep) {
  	Map<String, SingleStateExpression> stateMap = multiState.getStateMap();
  	String label = labelAnalyzer.getRepId(rep);
	  if(stateMap.containsKey(label)) return false;
	  
	  xtc.type.Type ptrRepType = labelAnalyzer.getRepType(rep);
  	SingleStateExpression singleState = singleStateFactory.freshSingleState(label, ptrRepType);
	  stateMap.put(label, singleState);	  
	  return false;
  }
}
