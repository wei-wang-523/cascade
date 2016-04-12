package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.annotation.Nullable;

import xtc.tree.Node;
import xtc.type.Type;

// import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Range;
import com.google.common.collect.Sets;
import com.google.inject.Inject;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.safety.IRMemSafetyEncoding;
import edu.nyu.cascade.ir.pass.IRAliasAnalyzer;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;

public class MultiLambdaStateFactory<T> extends AbstractStateFactory<T> {

	private final SingleLambdaStateFactory<T> singleStateFactory;
	IRAliasAnalyzer<T> labelAnalyzer;
	
  @Inject
	MultiLambdaStateFactory(ExpressionEncoding encoding, IRDataFormatter formatter,
      IRMemSafetyEncoding memSafetyEncoding) {
	  super(encoding, formatter);
	  singleStateFactory = createSingleLambda(encoding, formatter, memSafetyEncoding);
  }
  
	@Override
	public void reset() {}
	
	@Override
	public MultiLambdaStateExpression freshState() {
	  MultiLambdaStateExpression freshState = MultiLambdaStateExpression.create();
	  freshState.setMemTracker(getDataFormatter().getSizeZero());
	  return freshState;
	}
	
	@Override
	public void addStackVar(StateExpression state, Expression lval, IRVarInfo info) {
		if(!info.isStatic()) state.addVar(lval.asVariable());
		
		Node node = info.getDeclarationNode();
		labelAnalyzer.addStackVar(lval, node);		
		T rep = labelAnalyzer.getStackRep(node);
		long length = CType.getInstance().getSize(info.getXtcType());
		
		for(T fillInRep : labelAnalyzer.getFillInReps(rep, length)) {
			updateStateWithRep(state.asMultiLambda(), fillInRep);
			String label = labelAnalyzer.getRepId(fillInRep);
			SingleLambdaStateExpression singleState = state.asMultiLambda().getStateMap().get(label);
			xtc.type.Type lvalType = info.getXtcType();
			long size = getCTypeAnalyzer().getSize(lvalType);
			Expression sizeExpr = getExpressionEncoding().integerConstant(size);
			singleStateFactory.addStackVar(singleState, lval, sizeExpr);
		}
	}

	@Override
	public void addStackArray(StateExpression state, Expression lval,
			Expression rval, IRVarInfo info, Node sourceNode) {
		if(!info.isStatic()) state.addVar(lval.asVariable());
		
		labelAnalyzer.addStackVar(lval, sourceNode);
		T ptrRep = labelAnalyzer.getPointsToLoc(labelAnalyzer.getRep(sourceNode));
		long length = CType.getInstance().getSize(CType.getArrayCellType(info.getXtcType()));
		for(T rep : labelAnalyzer.getFillInReps(ptrRep, length)) {
			updateStateWithRep(state.asMultiLambda(), rep);
			String label = labelAnalyzer.getRepId(rep);
			SingleLambdaStateExpression singleState = state.asMultiLambda().getStateMap().get(label);
			singleStateFactory.updateSizeStateWithAlloc(singleState, lval, rval, sourceNode);
		}
		
		state.addConstraint(applyValidMalloc(state, lval, rval, sourceNode));
	}

	@Override
	public Expression lookupSize(StateExpression state, Expression ptr, Node node) {
		T rep = labelAnalyzer.getPointsToLoc(labelAnalyzer.getRep(node));
		String idxLabel = labelAnalyzer.getRepId(rep);
		
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
		updateStateWithRep(multiLambdaState, rep);
		SingleLambdaStateExpression singleLambdaState = multiLambdaState.getStateMap().get(idxLabel);
		ArrayExpression sizeArr = singleLambdaState.getSingleState().getSize();
		return getDataFormatter().indexSizeArray(sizeArr, ptr);
	}

	@Override
	public MultiLambdaStateExpression resolvePhiNode(Collection<StateExpression> preStates) {
		
		/* Build the joined state */
		Iterable<BooleanExpression> preGuards = Iterables.transform(preStates, pickGuard);
		MultiLambdaStateExpression joinState = joinPreStates(preStates, preGuards);
  	
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
		Collection<BooleanExpression> predicates = Lists.newArrayList();
		T rep = labelAnalyzer.getPointsToLoc(labelAnalyzer.getRep(ptrNode));
		Type ty = CType.getInstance().pointerize(CType.getType(ptrNode)).toPointer().getType();
		long length = CType.getInstance().getSize(ty);
		for(T fillInRep : labelAnalyzer.getFillInReps(rep, length)) {
			updateStateWithRep(state.asMultiLambda(), fillInRep);
			String label = labelAnalyzer.getRepId(fillInRep);
			SingleLambdaStateExpression singleState = state.asMultiLambda().getStateMap().get(label);
			predicates.add(singleStateFactory.applyMemset(singleState, region, size, value, null));
		}
		
		return getExpressionEncoding().and(predicates).asBooleanExpression();
	}
	
	@Override
	public BooleanExpression applyMemset(StateExpression state, Expression region,
			Expression size, int value, Node ptrNode) {	
		Collection<BooleanExpression> predicates = Lists.newArrayList();
		T rep = labelAnalyzer.getPointsToLoc(labelAnalyzer.getRep(ptrNode));
		Type ty = CType.getInstance().pointerize(CType.getType(ptrNode)).toPointer().getType();
		long length = CType.getInstance().getSize(ty);
		for(T fillInRep : labelAnalyzer.getFillInReps(rep, length)) {
			updateStateWithRep(state.asMultiLambda(), fillInRep);
			String label = labelAnalyzer.getRepId(fillInRep);
			SingleLambdaStateExpression singleState = state.asMultiLambda().getStateMap().get(label);
			predicates.add(singleStateFactory.applyMemset(singleState, region, size, value, null));
		}
		return getExpressionEncoding().and(predicates).asBooleanExpression();
	}

	@Override
	public BooleanExpression applyMemcpy(StateExpression state, Expression destRegion, 
			Expression srcRegion, Expression size, Node destNode, Node srcNode) {
		T destRep = labelAnalyzer.getPointsToLoc(labelAnalyzer.getRep(destNode));
		T srcRep = labelAnalyzer.getPointsToLoc(labelAnalyzer.getRep(srcNode));
		
		MultiLambdaStateExpression multiState = state.asMultiLambda();
		
		updateStateWithRep(multiState, destRep);
		updateStateWithRep(multiState, srcRep);
		
		String destLabel = labelAnalyzer.getRepId(destRep);
		String srcLabel = labelAnalyzer.getRepId(srcRep);
		SingleLambdaStateExpression destState = multiState.getStateMap().get(destLabel);
		SingleLambdaStateExpression srcState = multiState.getStateMap().get(srcLabel);
		
		ArrayExpression destMem = destState.getSingleState().getMemory();
		ArrayExpression srcMem = srcState.getSingleState().getMemory();
		
		IRDataFormatter formatter = getDataFormatter();
		return formatter.memoryCopy(destMem, srcMem, destRegion, srcRegion, size);
	}
	
	@Override
	public BooleanExpression applyValidMalloc(StateExpression state, Expression region, 
			Expression size, Node ptrNode) {
		T ptrRep = labelAnalyzer.getPointsToLoc(labelAnalyzer.getRep(ptrNode));
		updateStateWithRep(state.asMultiLambda(), ptrRep);
		String label = labelAnalyzer.getRepId(ptrRep);
		SingleLambdaStateExpression singleState = state.asMultiLambda().getStateMap().get(label);	
		return singleStateFactory.applyValidMalloc(singleState, region, size, ptrNode);
	}

	@Override
	public BooleanExpression applyValidFree(StateExpression state, Expression region, Node ptrNode) {
		T ptrRep = labelAnalyzer.getPointsToLoc(labelAnalyzer.getRep(ptrNode));
		updateStateWithRep(state.asMultiLambda(), ptrRep);
		String label = labelAnalyzer.getRepId(ptrRep);
		SingleLambdaStateExpression singleState = state.asMultiLambda().getStateMap().get(label);
		return singleStateFactory.applyValidFree(singleState, region, ptrNode);
	}

	@Override
	public BooleanExpression validAccess(StateExpression state, Expression ptr, Node ptrNode) {
		T srcRep = labelAnalyzer.getStackRep(ptrNode);
		MultiLambdaStateExpression multiState = state.asMultiLambda();
		updateStateWithRep(multiState, srcRep);
				
		String label = labelAnalyzer.getRepId(srcRep);
		SingleLambdaStateExpression singleState = multiState.getStateMap().get(label);
		BooleanExpression predicate = singleStateFactory.validAccess(singleState, ptr, ptrNode);
		
		return predicate;
	}

	@Override
	public BooleanExpression validAccessRange(StateExpression state, Expression ptr,
	    Expression size, Node ptrNode) {
		T srcRep = labelAnalyzer.getStackRep(ptrNode);
		updateStateWithRep(state.asMultiLambda(), srcRep);
		String label = labelAnalyzer.getRepId(srcRep);
		SingleLambdaStateExpression singleState = state.asMultiLambda().getStateMap().get(label);
		BooleanExpression predicate = singleStateFactory.validAccessRange(singleState, ptr, size, ptrNode);
		return predicate;
	}

	@Override
	protected BooleanExpression getDisjointAssumption(StateExpression state) {
		Map<String, SingleLambdaStateExpression> stateMap = state.asMultiLambda().getStateMap();
		Collection<BooleanExpression> preDisjoints = Lists.newArrayListWithCapacity(stateMap.size());
		
		for(SingleLambdaStateExpression subState : stateMap.values()) {
			preDisjoints.add(singleStateFactory.getDisjointAssumption(subState));
		}
		
		return getExpressionManager().and(preDisjoints);		
	}
	
	@Override
	public void malloc(StateExpression state, Expression ptr,
	    Expression size, Node ptrNode) {
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
		Expression multSize = getExpressionEncoding().times(nitem, size);
		VariableExpression region = createFreshRegion();
		state.addRegion(region);
		BooleanExpression tt = getExpressionEncoding().tt().asBooleanExpression();
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
	public void alloca(StateExpression state, Expression ptr,
	    Expression size, Node ptrNode) {
		VariableExpression region = createFreshRegion();
		state.addRegion(region);
		updateMemState(state, ptr, ptrNode, region, null);
		updateSizeStateWithAlloc(state, region, size, ptrNode);
		state.addConstraint(applyValidMalloc(state, region, size, ptrNode));
	}

	@SuppressWarnings("unchecked")
	@Override
	public <X> void setLabelAnalyzer(IRAliasAnalyzer<X> preprocessor) {
		labelAnalyzer = (IRAliasAnalyzer<T>) preprocessor;
	}
	
	@Override
	public void propagateState(StateExpression cleanState, StateExpression stateArg) {
		Collection<Expression> fromElems = Lists.newArrayList();
		Collection<Expression> toElems = Lists.newArrayList();
		Collection<Expression> fromPredicates = Lists.newArrayList();
		Collection<Expression> toPredicates = Lists.newArrayList();
		
		getSubstElemsPair(cleanState, stateArg, fromElems, toElems);
		substitute(cleanState, fromElems, toElems);
		
		cleanState.addPreGuard(stateArg.getGuard());
		cleanState.addConstraint(stateArg.getConstraint());
		
		getSubstPredicatesPair(cleanState, stateArg, fromPredicates, toPredicates);
		substPredicatesConstraint(cleanState, fromPredicates, toPredicates);
		substAssertions(cleanState, fromPredicates, toPredicates);
		
		propagateAssertions(stateArg, cleanState);
		propagateMemSafetyPredicates(stateArg, cleanState);
		propagateMemTracker(stateArg, cleanState);
		propagateNewSubState(stateArg, cleanState);
	}
	
	@Override
	public MultiLambdaStateExpression copy(StateExpression state) {
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
		
		Map<String, SingleLambdaStateExpression> stateMapCopy = Maps.newHashMap();
		
		for(Entry<String, SingleLambdaStateExpression> entry : multiLambdaState.getStateMap().entrySet()) {
			stateMapCopy.put(entry.getKey(), singleStateFactory.copy(entry.getValue()));
		}
		
		MultiLambdaStateExpression newState = MultiLambdaStateExpression.create(stateMapCopy);
		
		newState.setProperties(state.getProperties());
		newState.setConstraint(state.getConstraint());
		newState.setGuard(state.getGuard());
		
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
		substSafetyPredicates(state, vars, freshVars);
		substAssertions(state, vars, freshVars);
		substMemTracker(state, vars, freshVars);
	}
	
	@Override
	public Collection<BooleanExpression> getAssumptions() {
		return singleStateFactory.getAssumptions();
	}

	@Override
	protected void updateMarkState(StateExpression state,
			Expression region, BooleanExpression mark, Node ptrNode) {
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
		T ptrRep = labelAnalyzer.getPointsToLoc(labelAnalyzer.getRep(ptrNode));
		Type ty = CType.getInstance().pointerize(
				CType.getType(ptrNode)).toPointer().getType();
		long length = CType.getInstance().getSize(ty);
		for(T rep : labelAnalyzer.getFillInReps(ptrRep, length)) {
			updateStateWithRep(multiLambdaState, rep);
			String label = labelAnalyzer.getRepId(rep);
			SingleLambdaStateExpression singleState = multiLambdaState.getStateMap().get(label);
			singleStateFactory.updateMarkState(singleState, region, mark, ptrNode);
		}
	}
	
	@Override
	protected Expression getSizeOfRegion(StateExpression state, Expression region, Node ptrNode) {
		T ptrRep = labelAnalyzer.getPointsToLoc(labelAnalyzer.getRep(ptrNode));
		String label = labelAnalyzer.getRepId(ptrRep);
		
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();		
		Map<String, SingleLambdaStateExpression> statePrimeMap = multiLambdaState.getStateMap();
		SingleLambdaStateExpression singleState = statePrimeMap.get(label);
		
		ArrayExpression sizeArr = singleState.getSingleState().getSize();
		return getDataFormatter().indexSizeArray(sizeArr, region);
	}

	@Override
	protected void updateMemState(StateExpression state,
	    Expression index, Node idxNode, Expression value, @Nullable Node valNode) {
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();	
		Map<String, SingleLambdaStateExpression> stateMap = multiLambdaState.getStateMap();
		
		T rep = labelAnalyzer.getRep(idxNode);	
		
		/* The address should belongs to the group it points-to, where to reason
		 * about disjointness */
		xtc.type.Type idxType = CType.getType(idxNode);
		if(!CType.isScalar(idxType)) {
			rep = labelAnalyzer.getPointsToLoc(rep);
		}
		
		if(!(Preferences.isSet(Preferences.OPTION_FIELD_SENSITIVE) ||
				Preferences.isSet(Preferences.OPTION_CELL_BASED_FIELD_SENSITIVE) ||
				Preferences.isSet(Preferences.OPTION_CELL_BASED_FIELD_SENSITIVE_CONTEXT_SENSITIVE) ||
				Preferences.isSet(Preferences.OPTION_DSA))) {			
			updateStateWithRep(multiLambdaState, rep);
			String label = labelAnalyzer.getRepId(rep);
			SingleLambdaStateExpression singleState = stateMap.get(label);
			singleStateFactory.updateMemState(singleState, index, idxNode, value, valNode);
			return;
		}
		
		long length = CType.getInstance().getSize(idxType);
		Map<Range<Long>, T> fieldMap = labelAnalyzer.getStructMap(rep, length);
		
		if(fieldMap.isEmpty()) {			
			updateStateWithRep(multiLambdaState, rep);
			String label = labelAnalyzer.getRepId(rep);
			SingleLambdaStateExpression singleState = stateMap.get(label);
			
			if(!idxType.isStruct()) {
				singleStateFactory.updateMemState(singleState, index, idxNode, value, valNode);
			} else {
				CType cTypeAnalyzer = getCTypeAnalyzer();
				long range =  cTypeAnalyzer.getSize(idxType);
				singleStateFactory.updateStructInMemState(singleState, index, value, range);
			}
		} else {
			
			ExpressionEncoding encoding = getExpressionEncoding();
			
			for(Entry<Range<Long>, T> fieldEntry : fieldMap.entrySet()) {
				T fieldRep = labelAnalyzer.getPointsToLoc(fieldEntry.getValue());
				String fieldLabel = labelAnalyzer.getRepId(fieldRep);
				updateStateWithRep(multiLambdaState, fieldRep);
				SingleLambdaStateExpression singleState = stateMap.get(fieldLabel);
				
				long offset = fieldEntry.getKey().lowerEndpoint();
				Expression offExpr = encoding.integerConstant(offset);
				Expression indexOff = encoding.plus(index, offExpr);
				Expression valueOff = encoding.plus(value, offExpr);
				
				long range = fieldEntry.getKey().upperEndpoint() - offset;
				singleStateFactory.updateStructInMemState(singleState, indexOff, valueOff, range);
			}
		}
	}

	@Override
	protected void updateSizeStateWithFree(StateExpression state,
	    Expression region, Expression sizeVal, Node ptrNode) {
		T ptrRep = labelAnalyzer.getPointsToLoc(labelAnalyzer.getRep(ptrNode));
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
		Map<String, SingleLambdaStateExpression> stateMap = multiLambdaState.getStateMap();
		Type ty = CType.getInstance().pointerize(CType.getType(ptrNode)).toPointer().getType();
		long length = CType.getInstance().getSize(ty);
		for(T fillInRep : labelAnalyzer.getFillInReps(ptrRep, length)) {
			updateStateWithRep(multiLambdaState, fillInRep);
			String label = labelAnalyzer.getRepId(fillInRep);
			SingleLambdaStateExpression singleState = stateMap.get(label);
			singleStateFactory.updateSizeStateWithFree(singleState, region, sizeVal, ptrNode);
		}
	}

	@Override
	protected void updateSizeStateWithAlloc(
			StateExpression state, 
			Expression region, 
			Expression size,
			Node ptrNode) {
		T ptrRep = labelAnalyzer.getPointsToLoc(labelAnalyzer.getRep(ptrNode));
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
		labelAnalyzer.addAllocRegion(region, ptrNode);
		Type ty = CType.getInstance().pointerize(CType.getType(ptrNode)).toPointer().getType();
		long length = CType.getInstance().getSize(ty);
		for(T rep : labelAnalyzer.getFillInReps(ptrRep, length)) {
			updateStateWithRep(multiLambdaState, rep);
			String label = labelAnalyzer.getRepId(rep);
			SingleLambdaStateExpression singleState = multiLambdaState.getStateMap().get(label);
			singleStateFactory.updateSizeStateWithAlloc(singleState, region, size, ptrNode);
		}
	}
  
  @Override
	protected void substState(StateExpression state,
			Collection<? extends Expression> fromElems, Collection<? extends Expression> toElems) {
		if(fromElems.isEmpty()) return;
		
		/* Replace fromElems to toElems for every sub-state */
		Map<String, SingleLambdaStateExpression> stateMap = state.asMultiLambda().getStateMap();
			
		for(String name : stateMap.keySet()) {
			SingleLambdaStateExpression singleLambdaState = stateMap.get(name);
			singleStateFactory.substState(singleLambdaState, fromElems, toElems);
		}
	}

	@Override
	protected void propagateMemSafetyPredicates(StateExpression stateArg,
	    StateExpression cleanState) {
	  Map<String, SingleLambdaStateExpression> fromStateMap = stateArg.asMultiLambda().getStateMap();
	  Map<String, SingleLambdaStateExpression> toStateMap = cleanState.asMultiLambda().getStateMap();
	  	
	  Collection<String> commonNames = Sets.intersection(fromStateMap.keySet(), toStateMap.keySet());
	  if(commonNames.isEmpty()) return;
	  
	  for(String subStateName : commonNames) {
	  	SingleLambdaStateExpression fromSubState = fromStateMap.get(subStateName);
	  	SingleLambdaStateExpression toSubState = toStateMap.get(subStateName);
	  	singleStateFactory.propagateMemSafetyPredicates(fromSubState, toSubState);
	  }
	}

	@Override
	protected void getSubstElemsPair(
			StateExpression fromState, StateExpression toState,
			Collection<Expression> fromElems, Collection<Expression> toElems) {
		Map<String, SingleLambdaStateExpression> fromMap = fromState.asMultiLambda().getStateMap();
		Map<String, SingleLambdaStateExpression> toMap = toState.asMultiLambda().getStateMap();
	  Collection<String> commonNames = Sets.intersection(toMap.keySet(), fromMap.keySet());
	  
	  if(commonNames.isEmpty()) return;
	  
		for(String label : commonNames)
			singleStateFactory.getSubstElemsPair(
					fromMap.get(label), toMap.get(label), 
					fromElems, toElems);
		
	}

	@Override
	protected void getSubstPredicatesPair(
			StateExpression cleanState, StateExpression preState, 
			Collection<Expression> fromPredicates, Collection<Expression> toPredicates) {
		Map<String, SingleLambdaStateExpression> postStateMap = cleanState.asMultiLambda().getStateMap();
		Map<String, SingleLambdaStateExpression> preStateMap = preState.asMultiLambda().getStateMap();
	  Collection<String> commonNames = Sets.intersection(preStateMap.keySet(), postStateMap.keySet());
	  
	  if(commonNames.isEmpty()) return;
	  
		for(String label : commonNames) {
			singleStateFactory.getSubstPredicatesPair(
					postStateMap.get(label), preStateMap.get(label),
					fromPredicates, toPredicates);
		}
	}

	@Override
	protected MultiLambdaStateExpression joinPreStates(Iterable<StateExpression> preStates,
			Iterable<BooleanExpression> preGuards) {
		
		/* Collect all names */
		Collection<String> elemNames = Sets.newHashSet();
		for(StateExpression preState : preStates) {
			elemNames.addAll(preState.asMultiLambda().getStateMap().keySet());
		}
		
		if(elemNames.isEmpty()) return MultiLambdaStateExpression.create();
		
		/* Initialize state map of result state */
		Multimap<String, Pair<StateExpression, BooleanExpression>> resStateGuardMap =
				LinkedHashMultimap.create();
		
		/* Build state map */
		Iterator<BooleanExpression> preGuardItr = preGuards.iterator();
		for(StateExpression preState : preStates) {
			BooleanExpression guard = preGuardItr.next();
			
			Map<String, SingleLambdaStateExpression> preStateMap = preState.asMultiLambda().getStateMap();
			
			for(Entry<String, SingleLambdaStateExpression> entry : preStateMap.entrySet()) {
				String elemName = entry.getKey();
				StateExpression preElemState = entry.getValue();
				resStateGuardMap.put(elemName, Pair.of(preElemState, guard));
			}
		}
		
		int preStateSize = Iterables.size(preStates);
		
		/* build res state map */
		Map<String, SingleLambdaStateExpression> resStateMap = Maps.newHashMapWithExpectedSize(elemNames.size());
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
		  		ArrayType[] elemTypes = preElemStates.get(0).asSingleLambda().getSingleState().getElemTypes();
		  		preElemStates.add(0, singleStateFactory.freshSingleLambdaState(elemName, elemTypes));
		  		preElemGuards.add(0, null); // this guard will be ignored in join pre-states
		  	}
				
				SingleLambdaStateExpression singleState = singleStateFactory.joinPreStates(
						preElemStates, preElemGuards);
				resStateMap.put(elemName, singleState);
			}
		}
		
		return MultiLambdaStateExpression.create(resStateMap);
	}
	
	@Override
	protected Expression dereference(StateExpression state, Expression index, Node indexNode) {
		T rep = labelAnalyzer.getRep(indexNode);
		String idxLabel = labelAnalyzer.getRepId(rep);
		
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
		updateStateWithRep(multiLambdaState, rep);
		SingleLambdaStateExpression singleLambdaState = multiLambdaState.getStateMap().get(idxLabel);
		ArrayExpression memArr = singleLambdaState.getSingleState().getMemory();
		return getDataFormatter().indexMemoryArray(memArr, index, CType.getType(indexNode));
	}
	
  @Override
	protected void substSafetyPredicates(StateExpression state,
			Collection<? extends Expression> fromElems, Collection<? extends Expression> toElems) {
  	MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
  	Map<String, SingleLambdaStateExpression> stateMap = multiLambdaState.getStateMap();
  	
  	for(SingleLambdaStateExpression subState : stateMap.values()) {
  		singleStateFactory.substSafetyPredicates(subState, fromElems, toElems);
  	}
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
	  if(stateMap.containsKey(label)) return false;
	  
	  long width = labelAnalyzer.getRepTypeWidth(rep);
	  SingleLambdaStateExpression singleState = singleStateFactory.freshSingleLambdaState(label, width);
	  stateMap.put(label, singleState);
	  return false;
  }
}
