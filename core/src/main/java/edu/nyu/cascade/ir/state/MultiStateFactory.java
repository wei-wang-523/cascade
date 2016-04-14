package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.annotation.Nullable;

import xtc.tree.Node;
import xtc.type.Type;

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
import edu.nyu.cascade.ir.memory.IRPartitionHeapEncoder;
import edu.nyu.cascade.ir.pass.IRAliasAnalyzer;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;

public class MultiStateFactory<T> extends AbstractStateFactory<T> {

	private final SingleStateFactory<T> singleStateFactory;
	private final IRPartitionHeapEncoder heapEncoder;
	
	private IRAliasAnalyzer<T> labelAnalyzer;
	
  @Inject
	MultiStateFactory(ExpressionEncoding encoding, IRDataFormatter formatter, 
			IRPartitionHeapEncoder parHeapEncoder) {
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
	public <X> void setLabelAnalyzer(IRAliasAnalyzer<X> preprocessor) {
		labelAnalyzer = (IRAliasAnalyzer<T>) preprocessor;
	}
	
	@Override
	public MultiStateExpression freshState() {
	  MultiStateExpression freshState = MultiStateExpression.create();
	  freshState.setMemTracker(getDataFormatter().getSizeZero());
	  return freshState;
	}
	
	@Override
	public void addStackVar(StateExpression state, Expression lval, IRVarInfo info) {
		if(!info.isStatic()) state.addVar(lval.asVariable());
       
		Node node = info.getDeclarationNode();
		labelAnalyzer.addVar(lval, node);		
		T rep = labelAnalyzer.getStackRep(node);
		Type ty = CType.getInstance().pointerize(CType.getType(node));
		long length = CType.getInstance().getSize(ty);
		for(T fillInRep : labelAnalyzer.getFieldReps(rep, length)) {
			updateStateWithRep(state.asMultiple(), fillInRep);
			heapEncoder.addFreshAddress(labelAnalyzer.getRepId(fillInRep), lval, info);
		}
	}

	@Override
	public void addStackArray(StateExpression state, Expression lval,
			Expression rval, IRVarInfo info, Node sourceNode) {
		if(!info.isStatic()) state.addVar(lval.asVariable());
		
		labelAnalyzer.addVar(lval, sourceNode);
		T ptrRep = labelAnalyzer.getStackRep(sourceNode);
		long length = CType.getInstance().getSize(CType.getArrayCellType(info.getXtcType()));
		for(T rep : labelAnalyzer.getFieldReps(ptrRep, length)) {
			updateStateWithRep(state.asMultiple(), rep);
			String label = labelAnalyzer.getRepId(rep);
			SingleStateExpression singleState = state.asMultiple().getStateMap().get(label);
			singleStateFactory.updateSizeStateWithFree(singleState, lval, rval, sourceNode);
			heapEncoder.addFreshRegion(label, lval);
		}
		
		state.addConstraint(applyValidMalloc(state, lval, rval, sourceNode));
	}

	@Override
	public Expression lookupSize(StateExpression state, Expression ptr, Node node) {		
		T rep = labelAnalyzer.getPtsToRep(node);
		String label = labelAnalyzer.getRepId(rep);
		Map<String, SingleStateExpression> stateMap = state.asMultiple().getStateMap();
		SingleStateExpression singleState = stateMap.get(label);
		return getDataFormatter().indexSizeArray(singleState.getSize(), ptr);
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
	public BooleanExpression applyMemset(StateExpression state, Expression region, 
			Expression size, Expression value, Node ptrNode) {
		T srcRep = labelAnalyzer.getPtsToRep(ptrNode);
		updateStateWithRep(state.asMultiple(), srcRep);		
		String srcRepId = labelAnalyzer.getRepId(srcRep);
		SingleStateExpression singleState = state.asMultiple().getStateMap().get(srcRepId);
		return singleStateFactory.applyMemset(singleState, region, size, value, ptrNode);
	}
	  
	@Override
	public BooleanExpression applyMemset(StateExpression state, Expression region, 
			Expression size, int value, Node ptrNode) {
		T srcRep = labelAnalyzer.getPtsToRep(ptrNode);
		updateStateWithRep(state.asMultiple(), srcRep);
		String srcRepId = labelAnalyzer.getRepId(srcRep);
		SingleStateExpression singleState = state.asMultiple().getStateMap().get(srcRepId);
		return singleStateFactory.applyMemset(singleState, region, size, value, ptrNode);
	}	
	
	@Override
	public BooleanExpression applyMemcpy(StateExpression state, Expression destRegion, 
			Expression srcRegion, Expression size, Node destNode, Node srcNode) {
		T destRep = labelAnalyzer.getPtsToRep(destNode);
		T srcRep = labelAnalyzer.getPtsToRep(srcNode);
		
		updateStateWithRep(state.asMultiple(), destRep);
		updateStateWithRep(state.asMultiple(), srcRep);
		
		String destLabel = labelAnalyzer.getRepId(destRep);
		String srcLabel = labelAnalyzer.getRepId(srcRep);
		SingleStateExpression destState = state.asMultiple().getStateMap().get(destLabel);
		SingleStateExpression srcState = state.asMultiple().getStateMap().get(srcLabel);
		
		ArrayExpression destMem = destState.getMemory();
		ArrayExpression srcMem = srcState.getMemory();
		
		IRDataFormatter formatter = getDataFormatter();
		return formatter.memoryCopy(destMem, srcMem, destRegion, srcRegion, size);
	}

	@Override
	public BooleanExpression applyValidMalloc(StateExpression state, Expression ptr, 
			Expression size, Node pNode) {
		T srcRep = labelAnalyzer.getPtsToRep(pNode);		
		
		MultiStateExpression multiState = state.asMultiple();
		updateStateWithRep(multiState, srcRep);
		
		/* Get the related size array */
		String srcRepId = labelAnalyzer.getRepId(srcRep);
		SingleStateExpression singleState = multiState.getStateMap().get(srcRepId);
		ArrayExpression sizeArr = singleState.getSize();
		
		return heapEncoder.validMalloc(srcRepId, sizeArr, ptr, size);
	}

	@Override
	public BooleanExpression applyValidFree(StateExpression state, Expression region, Node ptrNode) {
		T srcRep = labelAnalyzer.getPtsToRep(ptrNode);
		updateStateWithRep(state.asMultiple(), srcRep);
		
		/* Get the related size array */
		String srcRepId = labelAnalyzer.getRepId(srcRep);
		SingleStateExpression singleState = state.asMultiple().getStateMap().get(srcRepId);
		ArrayExpression markArr = singleState.getMark();
		
		return heapEncoder.validFree(markArr, region);
	}

	@Override
	public BooleanExpression validAccess(StateExpression state, Expression ptr, Node ptrNode) {
		T srcRep = labelAnalyzer.getStackRep(ptrNode);		
		updateStateWithRep(state.asMultiple(), srcRep);
		
		/* Get the related size array */
		String srcRepId = labelAnalyzer.getRepId(srcRep);
		SingleStateExpression singleState = state.asMultiple().getStateMap().get(srcRepId);
		ArrayExpression sizeArr = singleState.getSize();
		
		return getExpressionManager().or(
				heapEncoder.validMemAccess(srcRepId, sizeArr, ptr));
	}

	@Override
	public BooleanExpression validAccessRange(StateExpression state, Expression ptr,
	    Expression size, Node ptrNode) {
		T srcRep = labelAnalyzer.getStackRep(ptrNode);
		updateStateWithRep(state.asMultiple(), srcRep);
		
		/* Get the related size array */
		String srcRepId = labelAnalyzer.getRepId(srcRep);
		SingleStateExpression singleState = state.asMultiple().getStateMap().get(srcRepId);
		ArrayExpression sizeArr = singleState.getSize();
	
		return getExpressionManager().or(
				heapEncoder.validMemAccess(srcRepId, sizeArr, ptr, size));
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
		propagateNewSubState(stateArg, cleanState);
	}

	@Override
	public MultiStateExpression copy(StateExpression state) {
		MultiStateExpression multiState = state.asMultiple();
		
		Map<String, SingleStateExpression> stateMapCopy = Maps.newHashMap();
		
		for(Entry<String, SingleStateExpression> entry : multiState.getStateMap().entrySet()) {
			stateMapCopy.put(entry.getKey(), singleStateFactory.copy(entry.getValue()));
		}
		
		MultiStateExpression newState = MultiStateExpression.create(stateMapCopy);
		
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
		substAssertions(state, vars, freshVars);
		substMemTracker(state, vars, freshVars);
	}
	
	@Override
	public Collection<BooleanExpression> getAssumptions() {
		return Collections.emptyList();
	}
	
	@Override
	protected void updateMarkState(StateExpression state,
			Expression region, BooleanExpression mark, Node ptrNode) {
		MultiStateExpression multiState = state.asMultiple();
		Map<String, SingleStateExpression> stateMap = multiState.getStateMap();
		
		T ptrRep = labelAnalyzer.getPtsToRep(ptrNode);
		Type ty = CType.getInstance().pointerize(CType.getType(ptrNode));
		long length = CType.getInstance().getSize(ty);
		for(T rep : labelAnalyzer.getFieldReps(ptrRep, length)) {
			updateStateWithRep(multiState, rep);
			String label = labelAnalyzer.getRepId(rep);
			SingleStateExpression singleState = stateMap.get(label);
			singleStateFactory.updateMarkState(singleState, region, mark, ptrNode);
		}
	}
	
	@Override
	protected BooleanExpression getDisjointAssumption(StateExpression state) {
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
	protected Expression getSizeOfRegion(StateExpression state, Expression region, Node ptrNode) {
		T ptrRep = labelAnalyzer.getPtsToRep(ptrNode);
		String label = labelAnalyzer.getRepId(ptrRep);
		
		Map<String, SingleStateExpression> stateMap = state.asMultiple().getStateMap();
		SingleStateExpression singleState = stateMap.get(label);
		
		ArrayExpression sizeArr = singleState.getSize();
		return getDataFormatter().indexSizeArray(sizeArr, region);
	}
	
  @Override
	protected void updateMemState(StateExpression state,
	    Expression index, Node idxNode, Expression value, @Nullable Node valNode) {
		MultiStateExpression multiState = state.asMultiple();
		Map<String, SingleStateExpression> stateMap = multiState.getStateMap();
		
		/* The address should belongs to the group it points-to, where to reason
		 * about disjointness */
		T rep = labelAnalyzer.getStackRep(idxNode);
		
		if(!(Preferences.isSet(Preferences.OPTION_FIELD_SENSITIVE) ||
				Preferences.isSet(Preferences.OPTION_CELL_BASED_FIELD_SENSITIVE) ||
				Preferences.isSet(Preferences.OPTION_CELL_BASED_FIELD_SENSITIVE_CONTEXT_SENSITIVE) ||
				Preferences.isSet(Preferences.OPTION_DSA))) {
			updateStateWithRep(multiState, rep);
			String label = labelAnalyzer.getRepId(rep);
			SingleStateExpression singleState = stateMap.get(label);
			singleStateFactory.updateMemState(singleState, index, idxNode, value, valNode);
			return;
		}
		
		xtc.type.Type idxType = CType.getType(idxNode);
		if(CType.isScalar(idxType)) {
			updateStateWithRep(multiState, rep);
			String label = labelAnalyzer.getRepId(rep);
			SingleStateExpression singleState = stateMap.get(label);
			singleStateFactory.updateMemState(singleState, index, idxNode, value, valNode);
		} else {
			ExpressionEncoding encoding = getExpressionEncoding();
			long length = CType.getInstance().getSize(idxType);
			Map<Range<Long>, T> fieldMap = labelAnalyzer.getStructMap(rep, length);
			for(Entry<Range<Long>, T> fieldEntry : fieldMap.entrySet()) {
				T fieldRep = labelAnalyzer.getPtsToFieldRep(fieldEntry.getValue());
				String fieldLabel = labelAnalyzer.getRepId(fieldRep);
				updateStateWithRep(multiState, fieldRep);
				SingleStateExpression singleState = stateMap.get(fieldLabel);
				
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
		T ptrRep = labelAnalyzer.getPtsToRep(ptrNode);
		MultiStateExpression multiState = state.asMultiple();
		Map<String, SingleStateExpression> stateMap = multiState.getStateMap();
		Type ty = CType.getInstance().pointerize(CType.getType(ptrNode));
		long length = CType.getInstance().getSize(ty);
		for(T rep : labelAnalyzer.getFieldReps(ptrRep, length)) {
			updateStateWithRep(multiState, rep);
			String label = labelAnalyzer.getRepId(rep);
			SingleStateExpression singleState = stateMap.get(label);
			singleStateFactory.updateSizeStateWithFree(singleState, region, sizeVal, ptrNode);
		}
	}

	@Override
	protected void updateSizeStateWithAlloc(StateExpression state,
			Expression region, Expression size, Node ptrNode) {
		T ptrRep = labelAnalyzer.getPtsToRep(ptrNode);
		MultiStateExpression multiState = state.asMultiple();
		labelAnalyzer.addRegion(region, ptrNode);
		Type ty = CType.getInstance().pointerize(CType.getType(ptrNode));
		long length = CType.getInstance().getSize(ty);
		for(T rep : labelAnalyzer.getFieldReps(ptrRep, length)) {
			updateStateWithRep(multiState, rep);
			String label = labelAnalyzer.getRepId(rep);
			SingleStateExpression singleState = multiState.getStateMap().get(label);
			singleStateFactory.updateSizeStateWithFree(singleState, region, size, ptrNode);
			heapEncoder.addFreshRegion(label, region);
		}
	}

	@Override
	protected void substState(StateExpression state,
			Collection<? extends Expression> fromElems, Collection<? extends Expression> toElems) {
		if(fromElems.isEmpty()) return;
		
		/* Substitution for every sub-state */
		Map<String, SingleStateExpression> stateMap = state.asMultiple().getStateMap();
		
		for(String name : stateMap.keySet()) {
			SingleStateExpression singleState = stateMap.get(name);
			singleStateFactory.substState(singleState, fromElems, toElems);
		}
	}

	@Override
	protected void propagateMemSafetyPredicates(StateExpression fromState,
	    StateExpression toState) {
	}

	@Override
	protected void getSubstElemsPair(
			StateExpression fromState, StateExpression toState,
			Collection<Expression> fromElems, Collection<Expression> toElems) {
		Map<String, SingleStateExpression> fromMap = fromState.asMultiple().getStateMap();
		Map<String, SingleStateExpression> toMap = toState.asMultiple().getStateMap();
	  Collection<String> commonNames = Sets.intersection(toMap.keySet(), fromMap.keySet());
	  
	  if(commonNames.isEmpty()) return;
	  
	  /* Get substitution pair of size array and memory elements */
		for(String label : commonNames)			
			singleStateFactory.getSubstElemsPair(
					fromMap.get(label), toMap.get(label), fromElems, toElems);
		
	}
	
	@Override
	protected void getSubstPredicatesPair(
			StateExpression fromState, StateExpression toState,
			Collection<Expression> fromPredicates, Collection<Expression> toPredicates) {
		// TODO Auto-generated method stub
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
		  		preElemStates.add(0, singleStateFactory.freshSingleState(elemName, elemTypes));
		  		preElemGuards.add(0, null); // this guard will be ignored in join pre-states
		  	}
				
				SingleStateExpression singleState = singleStateFactory.joinPreStates(preElemStates, preElemGuards);
				resStateMap.put(elemName, singleState);
			}
		}
		
		/* build res multi-state with constraint and guard */
		
		return MultiStateExpression.create(resStateMap);
	}

	@Override
	protected Expression dereference(StateExpression state, Expression index, Node indexNode) {
		T rep = labelAnalyzer.getRep(indexNode);
		String label = labelAnalyzer.getRepId(rep);
		
		updateStateWithRep(state.asMultiple(), rep);
		
		Map<String, SingleStateExpression> stateMap = state.asMultiple().getStateMap();
		SingleStateExpression singleState = stateMap.get(label);
		xtc.type.Type indexType = CType.getType(indexNode);
		return getDataFormatter().indexMemoryArray(singleState.getMemory(), index, indexType);
	}

	@Override
	protected void substSafetyPredicates(StateExpression state,
			Collection<? extends Expression> fromElems, Collection<? extends Expression> toElems) {
	  // TODO Auto-generated method stub
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
	  
	  long width = labelAnalyzer.getRepWidth(rep);
  	SingleStateExpression singleState = singleStateFactory.freshSingleState(label, width);
	  stateMap.put(label, singleState);	  
	  return false;
  }
}
