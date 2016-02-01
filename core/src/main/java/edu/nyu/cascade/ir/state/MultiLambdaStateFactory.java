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
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.LinkedHashMultimap;
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
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
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
	public void reset() {}
	
	@Override
	public MultiLambdaStateExpression freshState() {
	  return MultiLambdaStateExpression.create();
	}
	
	@Override
	public void addStackVar(StateExpression state, Expression lval, IRVarInfo info) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
		xtc.type.Type lvalType = info.getXtcType().resolve();
		Node node = info.getDeclarationNode();
		
		labelAnalyzer.addStackVar(lval, node);
		
		T rep;
		
		if(lvalType.isArray() || lvalType.isStruct() || lvalType.isUnion()) {
	  	rep = labelAnalyzer.getPointsToRep(node);
		} else {
			rep = labelAnalyzer.getRep(node);
		}
		
		MultiLambdaStateExpression multiState = state.asMultiLambda();
		
		updateStateWithRep(multiState, rep);
		
		String label = labelAnalyzer.getRepId(rep);
		SingleLambdaStateExpression singleState = multiState.getStateMap().get(label);
		
		long size = getCTypeAnalyzer().getSize(lvalType);
		Expression sizeExpr = getExpressionEncoding().integerConstant(size);
		singleStateFactory.addStackVar(singleState, lval, sizeExpr);
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
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptrNode);
		T srcRep = labelAnalyzer.getSrcRep(ptrRep);
		
		MultiLambdaStateExpression multiState = state.asMultiLambda();
		
		updateStateWithRep(multiState, srcRep);
		
		String label = labelAnalyzer.getRepId(srcRep);
		SingleLambdaStateExpression singleState = multiState.getStateMap().get(label);
		
		return singleStateFactory.applyMemset(singleState, region, size, value, ptrNode);
	}

	@Override
	public BooleanExpression applyMemcpy(StateExpression state, Expression destRegion, 
			Expression srcRegion, Expression size, Node destNode, Node srcNode) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
		T destPtrRep = labelAnalyzer.getPointsToRep(destNode);
		T destRep = labelAnalyzer.getSrcRep(destPtrRep);
		
		T srcPtrRep = labelAnalyzer.getPointsToRep(srcNode);
		T srcRep = labelAnalyzer.getSrcRep(srcPtrRep);
		
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
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptrNode);
		T srcRep = labelAnalyzer.getSrcRep(ptrRep);
		
		MultiLambdaStateExpression multiState = state.asMultiLambda();
		
		updateStateWithRep(multiState, srcRep);
		
		String label = labelAnalyzer.getRepId(srcRep);
		SingleLambdaStateExpression singleState = multiState.getStateMap().get(label);
		
	  return singleStateFactory.applyValidMalloc(singleState, region, size, ptrNode);
	}

	@Override
	public BooleanExpression applyValidFree(StateExpression state, Expression region, Node ptrNode) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptrNode);
		T srcRep = labelAnalyzer.getSrcRep(ptrRep);
		
		MultiLambdaStateExpression multiState = state.asMultiLambda();
		
		updateStateWithRep(multiState, srcRep);
		
		String label = labelAnalyzer.getRepId(srcRep);
		SingleLambdaStateExpression singleState = multiState.getStateMap().get(label);
		
		return singleStateFactory.applyValidFree(singleState, region, ptrNode);
	}

	@Override
	public BooleanExpression validAccess(StateExpression state, Expression ptr, Node ptrNode) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
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
		
		MultiLambdaStateExpression multiState = state.asMultiLambda();
		
		updateStateWithRep(multiState, srcRep);
		
		String label = labelAnalyzer.getRepId(srcRep);
		SingleLambdaStateExpression singleState = multiState.getStateMap().get(label);
		
		return singleStateFactory.validAccess(singleState, ptr, ptrNode);
	}

	@Override
	public BooleanExpression validAccessRange(StateExpression state, Expression ptr,
	    Expression size, Node ptrNode) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
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
		
		MultiLambdaStateExpression multiState = state.asMultiLambda();
		
		updateStateWithRep(multiState, srcRep);
		
		String label = labelAnalyzer.getRepId(srcRep);
		SingleLambdaStateExpression singleState = multiState.getStateMap().get(label);
		
		return singleStateFactory.validAccessRange(singleState, ptr, size, ptrNode);
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
	
	@Override
	public void malloc(StateExpression state, Expression ptr,
	    Expression size, Node ptrNode) {
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
	public void alloca(StateExpression state, Expression ptr,
	    Expression size, Node ptrNode) {
		Expression region = createFreshRegion();
		updateMemState(state, ptr, ptrNode, region, null);
		updateSizeStateWithAlloc(state, ptr, region, size, ptrNode);
		state.addConstraint(applyValidMalloc(state, region, size, ptrNode));
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
	public void propagateState(StateExpression cleanState,
	    StateExpression stateVar, StateExpression stateArg) {
		refreshDuplicateLabels(stateArg, cleanState);
		substitute(cleanState, stateVar, stateArg);
		cleanState.addPreGuard(stateArg.getGuard());
		cleanState.addConstraint(stateArg.getConstraint());
		
		propagateProperties(stateArg, cleanState);
		propagateNewSubState(stateArg, cleanState);
	}
	
	@Override
	public MultiLambdaStateExpression copy(StateExpression state) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
		
		Map<String, SingleLambdaStateExpression> stateMapCopy = Maps.newHashMap();
		
		for(Entry<String, SingleLambdaStateExpression> entry : multiLambdaState.getStateMap().entrySet()) {
			stateMapCopy.put(entry.getKey(), singleStateFactory.copy(entry.getValue()));
		}
		
		MultiLambdaStateExpression stateClone = MultiLambdaStateExpression.create(stateMapCopy);
		
		stateClone.setProperties(state.getProperties());
		stateClone.setConstraint(state.getConstraint());
		stateClone.setGuard(state.getGuard());
		
		return stateClone;
	}
	
	@Override
	public void initializeDefault(StateExpression state, Expression lval,
			Node lNode) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
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
		
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
		updateStateWithRep(multiLambdaState, rep);
	
		Map<String, SingleLambdaStateExpression> stateMap = multiLambdaState.getStateMap();
		SingleLambdaStateExpression singleState = stateMap.get(label);
		singleStateFactory.initializeDefault(singleState, lval, lNode);
	}
	
	@Override
	public void initializeValues(StateExpression state, Expression lval,
			Node lNode, List<Expression> rvals, List<Node> rNodes) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
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
		
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
		updateStateWithRep(multiLambdaState, rep);
	
		Map<String, SingleLambdaStateExpression> stateMap = multiLambdaState.getStateMap();
		SingleLambdaStateExpression singleState = stateMap.get(label);
		singleStateFactory.initializeValues(singleState, lval, lNode, rvals, rNodes);
	}
	
	@Override
	protected Expression getSizeOfRegion(StateExpression state, Expression region, Node ptrNode) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		T ptrRep = labelAnalyzer.getPointsToRep(ptrNode);
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
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
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
		
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
		updateStateWithRep(multiLambdaState, rep);
	
		Map<String, SingleLambdaStateExpression> stateMap = multiLambdaState.getStateMap();
		SingleLambdaStateExpression singleState = stateMap.get(label);
		singleStateFactory.updateMemState(singleState, index, idxNode, value, valNode);
	}

	@Override
	protected void updateSizeState(StateExpression state,
	    Expression region, Expression sizeVal, Node ptrNode) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptrNode);
		String regLabel = labelAnalyzer.getRepId(ptrRep);
		
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
		updateStateWithRep(multiLambdaState, ptrRep);
		
		Map<String, SingleLambdaStateExpression> stateMap = multiLambdaState.getStateMap();
		SingleLambdaStateExpression singleState = stateMap.get(regLabel);
		singleStateFactory.updateSizeState(singleState, region, sizeVal, ptrNode);
	}
	
	@Override
	protected void updateMarkState(StateExpression state,
	    Expression region, BooleanExpression mark, Node ptrNode) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptrNode);
		String regLabel = labelAnalyzer.getRepId(ptrRep);
		
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
		updateStateWithRep(multiLambdaState, ptrRep);
		
		Map<String, SingleLambdaStateExpression> stateMap = multiLambdaState.getStateMap();
		SingleLambdaStateExpression singleState = stateMap.get(regLabel);
		singleStateFactory.updateMarkState(singleState, region, mark, ptrNode);
	}

	@Override
	protected void updateSizeStateWithAlloc(
			StateExpression state, 
			Expression ptr, 
			Expression region, 
			Expression size,
			Node ptrNode) {
		Preconditions.checkArgument(state.isMultiple() || state.isLambda());
		
		T ptrRep = labelAnalyzer.getPointsToRep(ptrNode);
		String label = labelAnalyzer.getRepId(ptrRep);
		
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
		updateStateWithRep(multiLambdaState, ptrRep);
		
		labelAnalyzer.addAllocRegion(ptrRep, region, ptrNode);
		
		Map<String, SingleLambdaStateExpression> statePrimeMap = multiLambdaState.getStateMap();
		SingleLambdaStateExpression singleState = statePrimeMap.get(label);
		singleStateFactory.updateSizeStateWithAlloc(singleState, ptr, region, size, ptrNode);
	}
  
  @Override
	protected void doSubstitute(StateExpression state,
			final Collection<Expression> fromElems,
			final Collection<Expression> toElems,
			Collection<Expression> fromPredicates, 
			Collection<Expression> toPredicates) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
		if(fromElems.isEmpty() && fromPredicates.isEmpty()) return;
		
		if(!fromElems.isEmpty()) {
			
			/* Replace fromElems to toElems for every sub-state */
			MultiLambdaStateExpression lambdaState = state.asMultiLambda();
			Map<String, SingleLambdaStateExpression> stateMap = lambdaState.getStateMap();
			
			for(String name : stateMap.keySet()) {
				SingleLambdaStateExpression singleLambdaState = stateMap.get(name);
				SingleStateExpression singleState = singleLambdaState.getSingleState();
				
				 /* Substitute state elements */
				Expression newMem = singleState.getMemory().subst(fromElems, toElems);
				Expression newSize = singleState.getSize().subst(fromElems, toElems);
				Expression newMark = singleState.getMark().subst(fromElems, toElems);
				singleState.setMemory(newMem.asArray());
				singleState.setSize(newSize.asArray());
				singleState.setMark(newMark.asArray());
	
		    /* Substitute label table */
		    Table<VariableExpression, LabelType, Expression> labelTable = singleLambdaState.getLabelTable();
		    if(!labelTable.isEmpty()) {
		    	for(Cell<VariableExpression, LabelType, Expression> cell : ImmutableSet.copyOf(labelTable.cellSet())) {
		    		Expression value = cell.getValue();
		    		Expression valuePrime = value.subst(fromElems, toElems);
		    		labelTable.put(cell.getRowKey(), cell.getColumnKey(), valuePrime);
		    	}
		    }
			}
		}
		
		Collection<Expression> fromExprs = Lists.newArrayList();
	  fromExprs.addAll(fromElems);
	  fromExprs.addAll(fromPredicates);
	  
		Collection<Expression> toExprs = Lists.newArrayList();
		toExprs.addAll(toElems);
		toExprs.addAll(toPredicates);
	
		if(fromExprs.isEmpty()) return;
		
		if(state.getConstraint() != null) { /* Substitute constraint */
			BooleanExpression pc = state.getConstraint();
			pc = pc.subst(fromExprs, toExprs).asBooleanExpression();
			state.setConstraint(pc);
		}  
			
		/* Substitute guards */
		BooleanExpression guard = state.getGuard();
		guard = guard.subst(fromExprs, toExprs).asBooleanExpression();
		state.setGuard(guard);
	}

	@Override
	protected void propagateProperties(StateExpression fromState,
	    StateExpression toState) {
		Preconditions.checkArgument(fromState.isMultiple() && fromState.isLambda());
		Preconditions.checkArgument(toState.isMultiple() && toState.isLambda());
		
	  Map<String, SingleLambdaStateExpression> fromStateMap = fromState.asMultiLambda().getStateMap();
	  Map<String, SingleLambdaStateExpression> toStateMap = toState.asMultiLambda().getStateMap();
	  	
	  Collection<String> commonNames = Sets.intersection(fromStateMap.keySet(), toStateMap.keySet());
	  if(commonNames.isEmpty()) return;
	  
	  for(String subStateName : commonNames) {
	  	SingleLambdaStateExpression fromSubState = fromStateMap.get(subStateName);
	  	SingleLambdaStateExpression toSubState = toStateMap.get(subStateName);
	  	singleStateFactory.propagateProperties(fromSubState, toSubState);
	  }
	  
	  return;
	}

	@Override
	protected Pair<List<Expression>, List<Expression>> getSubstElemsPair(
			StateExpression fromState, StateExpression toState) {
		Preconditions.checkArgument(fromState.isMultiple() && fromState.isLambda());
		Preconditions.checkArgument(toState.isMultiple() && toState.isLambda());
		
		Map<String, SingleLambdaStateExpression> fromMap = fromState.asMultiLambda().getStateMap();
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
		doSubstitute(state, substElemsPair.fst(), substElemsPair.snd(),
				substPredsPair.fst(), substPredsPair.snd());
	}
	
	@Override
	protected Expression dereference(StateExpression state, Expression index, Node indexNode) {
		Preconditions.checkArgument(state.isMultiple() && state.isLambda());
		
		T rep = labelAnalyzer.getRep(indexNode);
		String idxLabel = labelAnalyzer.getRepId(rep);
		
		MultiLambdaStateExpression multiLambdaState = state.asMultiLambda();
		updateStateWithRep(multiLambdaState, rep);
		SingleLambdaStateExpression singleLambdaState = multiLambdaState.getStateMap().get(idxLabel);
		ArrayExpression memArr = singleLambdaState.getSingleState().getMemory();
		return getDataFormatter().indexMemoryArray(memArr, index, CType.getType(indexNode));
	}

	@Override
	protected Expression eval(Expression expr, StateExpression stateVar,
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
		
		Expression exprPrime = fromExprs.isEmpty() ? expr : expr.subst(fromExprs, toExprs);
		return exprPrime;
	}

	/**
	 * Find the duplicate labels between <code>fromState</code> and <code>toState</code>,
	 * generate fresh labels for them, and replace old labels to fresh labels in everything 
	 * may contains those labels. 
	 * 
	 * @param fromState
	 * @param toState
	 * @return
	 */
	void refreshDuplicateLabels(StateExpression fromState,
	    StateExpression toState) {
		Preconditions.checkArgument(fromState.isMultiple() && fromState.isLambda());
		Preconditions.checkArgument(toState.isMultiple() && toState.isLambda());
		
		/* Collect label replace pair and expression replace pair */
		
		Map<String, SingleLambdaStateExpression> fromStateMap = fromState.asMultiLambda().getStateMap();
		Map<String, SingleLambdaStateExpression> toStateMap = toState.asMultiLambda().getStateMap();
		
		Collection<String> commonSubStateNames = Sets.intersection(fromStateMap.keySet(), toStateMap.keySet());
		
		if(commonSubStateNames.isEmpty()) return;
		
		/* Store the single state name and its duplicated label pairs */
		Map<String, Pair<Collection<VariableExpression>, Collection<VariableExpression>>> subStateLabelPairMap = 
				Maps.newHashMapWithExpectedSize(commonSubStateNames.size());
		final Collection<Expression> fromExprs = Lists.newArrayList();
		final Collection<Expression> toExprs = Lists.newArrayList();
		
		for(String subStateName : commonSubStateNames) {
			SingleLambdaStateExpression fromSubState = fromStateMap.get(subStateName);
			SingleLambdaStateExpression toSubState = toStateMap.get(subStateName);
			
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
		
		if(subStateLabelPairMap.isEmpty()) return;
		
		/* Update every sub-state */
		
		for(String subStateName : ImmutableSet.copyOf(toStateMap.keySet())) {
			SingleLambdaStateExpression singleLambdaState = toStateMap.get(subStateName);
			SingleStateExpression singleState = singleLambdaState.getSingleState();
			
		  /* Update state elements */
			Expression newMem = singleState.getMemory().subst(fromExprs, toExprs);
			Expression newSize = singleState.getSize().subst(fromExprs, toExprs);
			Expression newMark = singleState.getMark().subst(fromExprs, toExprs);
			singleState.setMemory(newMem.asArray());
			singleState.setSize(newSize.asArray());
			singleState.setMark(newMark.asArray());
			
			/* Without duplicated labels, no need to update the label table */
			if(!subStateLabelPairMap.containsKey(subStateName)) continue;
			
			/* With duplicated labels and the label table should be updated */
			Pair<Collection<VariableExpression>, Collection<VariableExpression>> labelPair = 
					subStateLabelPairMap.get(subStateName);
			Collection<VariableExpression> fromLabels = labelPair.fst();
			Collection<VariableExpression> toLabels = labelPair.snd();
			
			/* Update label table */
			singleStateFactory.refreshLabelTable(singleLambdaState.getLabelTable(), 
					fromLabels, toLabels, fromExprs, toExprs);
			
			/* Refresh duplicate labels in safety properties */
			memSafetyEncoding.refreshDuplicateLabels(singleLambdaState, fromLabels, toLabels);
		}
		
		/* Constraint and guard may contain the old labels, needs to be updated */
		for(Pair<Collection<VariableExpression>, Collection<VariableExpression>> labelPair 
				: subStateLabelPairMap.values()) {
			fromExprs.addAll(labelPair.fst()); toExprs.addAll(labelPair.snd());
		}
		
		if(toState.getConstraint() != null) { /* Update constraint */
	  	BooleanExpression pc = toState.getConstraint();
	  	BooleanExpression pcPrime = pc.subst(fromExprs, toExprs).asBooleanExpression();
	  	toState.setConstraint(pcPrime);
	  }
	  
	  { /* Update guard */
	  	BooleanExpression guard = toState.getGuard();
	  	BooleanExpression guardPrime = guard.subst(fromExprs, toExprs).asBooleanExpression();
	  	toState.setGuard(guardPrime);
	  }
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
		
		for(String label : newSubStateNamesInFromState) {
			toMap.put(label, fromMap.get(label));
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
  	
  	SingleLambdaStateExpression singleState;
	  if(stateMap.containsKey(label)) return false;
	  
	  xtc.type.Type ptrRepType = labelAnalyzer.getRepType(rep);
	  singleState = singleStateFactory.freshSingleLambdaState(label, ptrRepType);
	  stateMap.put(label, singleState);
	  
	  return false;
  }
}
