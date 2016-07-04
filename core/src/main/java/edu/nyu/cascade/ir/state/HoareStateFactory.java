package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;

import javax.annotation.Nullable;

import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.inject.Inject;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.pass.IRAliasAnalyzer;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;

public class HoareStateFactory<T> implements StateFactory<T> {

	private final AbstractStateFactory<T> stateFactory;

	@Inject
	private HoareStateFactory(AbstractStateFactory<T> _stateFactory) {
		stateFactory = _stateFactory;
	}

	public static <T> StateFactory<T> create(
	    AbstractStateFactory<T> _stateFactory) {
		return new HoareStateFactory<T>(_stateFactory);
	}

	@Override
	public void reset() {
		stateFactory.reset();
	}

	@Override
	public StateExpression resolvePhiNode(Collection<StateExpression> preStates) {
		StateExpression state = stateFactory.resolvePhiNode(preStates);

		int preStatesSize = preStates.size();
		Map<Expression, Multimap<Expression, BooleanExpression>> hoareGuardTable = Maps
		    .newHashMap();

		for (StateExpression preState : preStates) {
			BooleanExpression guard = preState.getGuard();

			Map<Expression, Expression> hoareMap = preState.getHoareValues();
			for (Entry<Expression, Expression> entry : hoareMap.entrySet()) {
				Expression key = entry.getKey();
				Expression value = entry.getValue();

				Multimap<Expression, BooleanExpression> hoareGuardMap;
				if (hoareGuardTable.containsKey(key)) {
					hoareGuardMap = hoareGuardTable.get(key);
				} else {
					hoareGuardMap = LinkedHashMultimap.create();
					hoareGuardTable.put(key, hoareGuardMap);
				}
				hoareGuardMap.put(value, guard);
			}
		}

		Collection<Expression> keySet = hoareGuardTable.keySet();
		Map<Expression, Expression> joinHoareMap = Maps.newHashMapWithExpectedSize(
		    keySet.size());
		ExpressionEncoding encoding = getExpressionEncoding();
		for (Expression key : keySet) {
			Multimap<Expression, BooleanExpression> guardHoareMap = hoareGuardTable
			    .get(key);
			Expression joinValue;
			if (guardHoareMap.size() < preStatesSize) {
				Expression defaultValue = encoding.getRvalBinding(key);
				joinValue = stateFactory.getITEExpressionWithDefaultValue(guardHoareMap,
				    defaultValue);
			} else {
				joinValue = stateFactory.getITEExpression(guardHoareMap);
			}
			joinHoareMap.put(key, joinValue);
		}

		state.setHoareValues(joinHoareMap);
		return state;
	}

	@Override
	public BooleanExpression applyValidMalloc(StateExpression state,
	    Expression ptr, Expression size, Node pNode) {
		return stateFactory.applyValidMalloc(state, ptr, size, pNode);
	}

	@Override
	public BooleanExpression applyValidFree(StateExpression state, Expression ptr,
	    Node pNode) {
		return stateFactory.applyValidFree(state, ptr, pNode);
	}

	@Override
	public BooleanExpression applyMemoryTrack(StateExpression state) {
		return stateFactory.applyMemoryTrack(state);
	}

	@Override
	public BooleanExpression applyMemset(StateExpression state, Expression region,
	    Expression size, Expression value, Node ptrNode) {
		return stateFactory.applyMemset(state, region, size, value, ptrNode);
	}

	@Override
	public BooleanExpression applyMemset(StateExpression state, Expression region,
	    Expression size, int value, Node ptrNode) {
		return stateFactory.applyMemset(state, region, size, value, ptrNode);
	}

	@Override
	public BooleanExpression applyMemcpy(StateExpression state,
	    Expression destRegion, Expression srcRegion, Expression size,
	    Node destNode, Node srcNode) {
		return stateFactory.applyMemcpy(state, destRegion, srcRegion, size,
		    destNode, srcNode);
	}

	@Override
	public BooleanExpression validAccess(StateExpression state, Expression ptr,
	    Node pNode) {
		if (ptr.isHoareLogic())
			return stateFactory.getExpressionManager().tt();
		else
			return stateFactory.validAccess(state, ptr, pNode);
	}

	@Override
	public BooleanExpression validAccessRange(StateExpression state,
	    Expression ptr, Expression size, Node pNode) {
		return stateFactory.validAccessRange(state, ptr, size, pNode);
	}

	@Override
	public IRDataFormatter getDataFormatter() {
		return stateFactory.getDataFormatter();
	}

	@Override
	public ExpressionEncoding getExpressionEncoding() {
		return stateFactory.getExpressionEncoding();
	}

	@Override
	public void malloc(StateExpression state, Expression ptr, Expression size,
	    Node ptrNode) {
		if (ptr.isHoareLogic()) {
			VariableExpression region = stateFactory.createFreshRegion();
			state.addRegion(region);
			BooleanExpression tt = getExpressionEncoding().tt().asBooleanExpression();
			updateHoareMemState(state, ptr, ptrNode, region, null);
			stateFactory.updateSizeStateWithAlloc(state, region, size, ptrNode);
			stateFactory.updateMarkState(state, region, tt, ptrNode);
			stateFactory.plusRegionSize(state, size);
			state.addConstraint(applyValidMalloc(state, region, size, ptrNode));
		} else {
			stateFactory.malloc(state, ptr, size, ptrNode);
		}
	}

	@Override
	public void calloc(StateExpression state, Expression ptr, Expression nitem,
	    Expression size, Node ptrNode) {
		if (ptr.isHoareLogic()) {
			ExpressionEncoding encoding = getExpressionEncoding();

			VariableExpression region = stateFactory.createFreshRegion();
			state.addRegion(region);
			Expression multSize = encoding.times(nitem, size);
			BooleanExpression tt = encoding.tt().asBooleanExpression();

			updateHoareMemState(state, ptr, ptrNode, region, null);
			stateFactory.updateSizeStateWithAlloc(state, region, multSize, ptrNode);
			stateFactory.updateMarkState(state, region, tt, ptrNode);
			stateFactory.plusRegionSize(state, multSize);
			state.addConstraint(applyValidMalloc(state, region, multSize, ptrNode));
			state.addConstraint(applyMemset(state, region, multSize,
			    getExpressionEncoding().characterConstant(0), ptrNode));
		} else {
			stateFactory.calloc(state, ptr, nitem, size, ptrNode);
		}
	}

	@Override
	public void alloca(StateExpression state, Expression ptr, Expression size,
	    Node ptrNode) {
		if (ptr.isHoareLogic()) {
			VariableExpression region = stateFactory.createFreshRegion();
			state.addRegion(region);
			updateHoareMemState(state, ptr, ptrNode, region, null);
			stateFactory.updateSizeStateWithAlloc(state, region, size, ptrNode);
			state.addConstraint(applyValidMalloc(state, region, size, ptrNode));
		} else {
			stateFactory.alloca(state, ptr, size, ptrNode);
		}
	}

	@Override
	public void assign(StateExpression state, Expression memIdx, Node idxNode,
	    Expression memVal, Node valNode) {
		if (memIdx.isHoareLogic()) {
			updateHoareMemState(state, memIdx, idxNode, memVal, valNode);
		} else {
			stateFactory.assign(state, memIdx, idxNode, memVal, valNode);
		}
	}

	@Override
	public void free(StateExpression state, Expression region, Node ptrNode) {
		stateFactory.free(state, region, ptrNode);
	}

	@Override
	public Expression deref(StateExpression state, Expression memIdx,
	    Node memIdxNode) {
		if (memIdx.isHoareLogic()) {
			Map<Expression, Expression> hoareMap = state.getHoareValues();
			return hoareMap.containsKey(memIdx) ? hoareMap.get(memIdx)
			    : stateFactory.getExpressionEncoding().getRvalBinding(memIdx);
		} else {
			return stateFactory.deref(state, memIdx, memIdxNode);
		}
	}

	@Override
	public Expression lookupSize(StateExpression state, Expression ptr,
	    Node node) {
		return stateFactory.lookupSize(state, ptr, node);
	}

	@Override
	public StateExpression freshState() {
		return stateFactory.freshState();
	}

	@Override
	public void addStackVar(StateExpression state, Expression lval,
	    IRVarInfo info) {
		if (lval.isHoareLogic()) {
			if (!info.isStatic())
				state.addVar(lval.asVariable());
		} else {
			long size = stateFactory.getCTypeAnalyzer().getSize(info.getXtcType());
			if (size == 0)
				return;
			stateFactory.addStackVar(state, lval, info);
		}
	}

	@Override
	public void addStackArray(StateExpression state, Expression lval,
	    Expression rval, IRVarInfo info, Node sourceNode) {
		stateFactory.addStackArray(state, lval, rval, info, sourceNode);
	}

	@Override
	public <X> void setLabelAnalyzer(IRAliasAnalyzer<X> preprocessor) {
		stateFactory.setLabelAnalyzer(preprocessor);
	}

	@Override
	public void propagateState(StateExpression cleanState,
	    StateExpression stateArg) {
		Collection<Expression> fromElems = Lists.newArrayList();
		Collection<Expression> toElems = Lists.newArrayList();
		Collection<Expression> fromPredicates = Lists.newArrayList();
		Collection<Expression> toPredicates = Lists.newArrayList();

		stateFactory.getSubstElemsPair(cleanState, stateArg, fromElems, toElems);
		getSubstVars(stateArg, fromElems, toElems);
		substitute(cleanState, fromElems, toElems);

		cleanState.addPreGuard(stateArg.getGuard());
		cleanState.addConstraint(stateArg.getConstraint());

		stateFactory.getSubstPredicatesPair(cleanState, stateArg, fromPredicates,
		    toPredicates);
		stateFactory.substPredicatesConstraint(cleanState, fromPredicates,
		    toPredicates);
		stateFactory.substAssertions(cleanState, fromPredicates, toPredicates);

		stateFactory.propagateAssertions(stateArg, cleanState);

		stateFactory.propagateMemSafetyPredicates(stateArg, cleanState);
		propagateMap(stateArg, cleanState);

		stateFactory.propagateMemTracker(stateArg, cleanState);

		if (stateArg.isMultiple())
			stateFactory.propagateNewSubState(stateArg, cleanState);
	}

	@Override
	public StateExpression copy(StateExpression state) {
		StateExpression stateClone = stateFactory.copy(state);
		Map<Expression, Expression> hoareMap = state.getHoareValues();
		stateClone.setHoareValues(hoareMap);
		return stateClone;
	}

	@Override
	public void substitute(StateExpression state,
	    Collection<? extends Expression> fromElems,
	    Collection<? extends Expression> toElems) {
		if (fromElems.isEmpty())
			return;
		stateFactory.substitute(state, fromElems, toElems);
		substHoareMap(state, fromElems, toElems);
	}

	@Override
	public void setValidAccess(StateExpression pre, Expression lhsExpr,
	    Node lNode) {
		if (!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK))
			return;
		if (lhsExpr.isHoareLogic())
			return;

		BooleanExpression validAccess = validAccess(pre, lhsExpr, lNode);
		BooleanExpression tt = stateFactory.getExpressionManager().tt();
		if (validAccess.equals(tt))
			return;

		BooleanExpression assertion = stateToBoolean(pre).implies(validAccess);
		pre.addAssertion(Identifiers.VALID_DEREF, assertion);
	}

	@Override
	public void setValidAccessRange(StateExpression pre, Expression lhsExpr,
	    Expression sizeExpr, Node lNode) {
		if (!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK))
			return;
		if (lhsExpr.isHoareLogic())
			return;

		BooleanExpression validAccess = validAccessRange(pre, lhsExpr, sizeExpr,
		    lNode);
		BooleanExpression tt = stateFactory.getExpressionManager().tt();
		if (validAccess.equals(tt))
			return;

		BooleanExpression assertion = stateToBoolean(pre).implies(validAccess);
		pre.addAssertion(Identifiers.VALID_DEREF, assertion);
	}

	@Override
	public void setValidFree(StateExpression pre, Expression regionExpr,
	    Node ptrNode) {
		if (!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK))
			return;
		BooleanExpression validFree = applyValidFree(pre, regionExpr, ptrNode);
		BooleanExpression tt = stateFactory.getExpressionManager().tt();
		if (validFree.equals(tt))
			return;

		BooleanExpression assertion = stateToBoolean(pre).implies(validFree);
		pre.addAssertion(Identifiers.VALID_FREE, assertion);
	}

	@Override
	public final BooleanExpression stateToBoolean(StateExpression state) {
		return stateFactory.stateToBoolean(state);
	}

	@Override
	public final Collection<BooleanExpression> getAssumptions() {
		return stateFactory.getAssumptions();
	}

	private void updateHoareMemState(StateExpression state, Expression index,
	    Node idxNode, Expression value, @Nullable Node valNode) {
		Preconditions.checkArgument(index.isHoareLogic());
		ExpressionEncoding encoding = stateFactory.getExpressionEncoding();

		xtc.type.Type idxType = CType.getType(idxNode);
		if (idxType.resolve().isBoolean()) {
			value = encoding.castToBoolean(value);
		} else {
			boolean isUnsigned = valNode != null && CType.isUnsigned(CType.getType(
			    valNode));
			int size = (int) stateFactory.getCTypeAnalyzer().getWidth(idxType);
			value = encoding.castToInteger(value, size, !isUnsigned);
		}
		state.updateHoareValue(index, value);
	}

	private void substHoareMap(StateExpression state,
	    Collection<? extends Expression> fromElems,
	    Collection<? extends Expression> toElems) {
		Map<Expression, Expression> hoareMap = state.getHoareValues();
		for (Expression idx : ImmutableSet.copyOf(hoareMap.keySet())) {
			Expression value = hoareMap.remove(idx);
			Expression idxPrime = idx.subst(fromElems, toElems);
			idxPrime.setHoareLogic(idx.isHoareLogic());
			Expression valuePrime = value.subst(fromElems, toElems);
			hoareMap.put(idxPrime, valuePrime);
		}
	}

	private void propagateMap(StateExpression fromState,
	    StateExpression toState) {
		Map<Expression, Expression> fromHoareMap = fromState.getHoareValues();
		Map<Expression, Expression> toHoareMap = toState.getHoareValues();

		for (Expression idx : fromHoareMap.keySet()) {
			if (toHoareMap.containsKey(idx))
				continue;
			toHoareMap.put(idx, fromHoareMap.get(idx));
		}
	}

	private void getSubstVars(StateExpression state,
	    Collection<Expression> fromElems, Collection<Expression> toElems) {
		Map<Expression, Expression> hoareMap = state.getHoareValues();
		ExpressionEncoding encoding = stateFactory.getExpressionEncoding();
		for (Entry<Expression, Expression> entry : hoareMap.entrySet()) {
			Expression key = encoding.getRvalBinding(entry.getKey());
			Expression expr = entry.getValue();
			fromElems.add(key);
			toElems.add(expr);
		}
	}
}