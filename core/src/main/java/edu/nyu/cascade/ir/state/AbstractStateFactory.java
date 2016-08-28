package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;

import javax.annotation.Nullable;

import xtc.tree.Node;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import com.google.inject.Inject;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.IRPartitionHeapEncoder;
import edu.nyu.cascade.ir.memory.IRSingleHeapEncoder;
import edu.nyu.cascade.ir.memory.safety.IRMemSafetyEncoding;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;

public abstract class AbstractStateFactory<T> implements StateFactory<T> {
	protected static final String REGION_VARIABLE_NAME = "CASCADE_region";
	protected static final String DEFAULT_MEMORY_VARIABLE_NAME = "CASCADE_m";
	protected static final String DEFAULT_SIZE_VARIABLE_NAME = "CASCADE_size";
	protected static final String DEFAULT_MARK_VARIABLE_NAME = "CASCADE_mark";

	protected static Function<StateExpression, BooleanExpression> pickGuard = new Function<StateExpression, BooleanExpression>() {
		@Override
		public BooleanExpression apply(StateExpression state) {
			return state.getGuard();
		}
	};

	private final CType cTypeAnalyzer;
	private final ExpressionEncoding encoding;
	private final IRDataFormatter formatter;

	@Inject
	public AbstractStateFactory(ExpressionEncoding encoding,
			IRDataFormatter formatter) {
		this.encoding = encoding;
		this.formatter = formatter;
		this.cTypeAnalyzer = encoding.getCTypeAnalyzer();
	}

	public static <T> SingleLambdaStateFactory<T> createSingleLambda(
			ExpressionEncoding encoding, IRDataFormatter formatter,
			IRMemSafetyEncoding memSafetyEncoding) {
		return new SingleLambdaStateFactory<T>(encoding, formatter,
				memSafetyEncoding);
	}

	public static <T> MultiStateFactory<T> createMultiple(
			ExpressionEncoding encoding, IRDataFormatter formatter,
			IRPartitionHeapEncoder heapEncoder) {
		return new MultiStateFactory<T>(encoding, formatter, heapEncoder);
	}

	public static <T> SingleStateFactory<T> createSingle(
			ExpressionEncoding encoding, IRDataFormatter formatter,
			IRSingleHeapEncoder heapEncoder) {
		return new SingleStateFactory<T>(encoding, formatter, heapEncoder);
	}

	public static <T> MultiLambdaStateFactory<T> createMultipleLambda(
			ExpressionEncoding encoding, IRDataFormatter formatter,
			IRMemSafetyEncoding memSafetyEncoding) {
		return new MultiLambdaStateFactory<T>(encoding, formatter,
				memSafetyEncoding);
	}

	static <T> SingleStateFactory<T> createSingle(ExpressionEncoding encoding,
			IRDataFormatter formatter) {
		return new SingleStateFactory<T>(encoding, formatter, null);
	}

	CType getCTypeAnalyzer() {
		return cTypeAnalyzer;
	}

	@Override
	public IRDataFormatter getDataFormatter() {
		return formatter;
	}

	@Override
	public ExpressionEncoding getExpressionEncoding() {
		return encoding;
	}

	@Override
	public void free(StateExpression state, Expression region, Node ptrNode) {
		minusRegionSize(state, region, ptrNode);
		Expression sizeZro = formatter.getSizeZero();
		updateSizeStateWithFree(state, region, sizeZro, ptrNode);
		BooleanExpression ff = getExpressionEncoding().ff().asBooleanExpression();
		updateMarkState(state, region, ff, ptrNode);
	}

	@Override
	public void assign(StateExpression state, Expression index, Node idxNode,
			Expression value, Node valNode) {
		updateMemState(state, index, idxNode, value, valNode);
	}

	@Override
	public Expression deref(StateExpression state, Expression index,
			Node idxNode) {
		return dereference(state, index, idxNode);
	}

	@Override
	public BooleanExpression applyMemoryTrack(StateExpression state) {
		Expression memTracker = state.getMemTracker();
		Expression zero = formatter.getSizeZero();
		BooleanExpression tt = getExpressionManager().tt();
		if (memTracker.equals(zero))
			return tt;

		return zero.eq(memTracker);
	}

	@Override
	public void setValidAccess(StateExpression pre, Expression lhsExpr,
			Node lNode) {
		if (!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK))
			return;
		BooleanExpression validAccess = validAccess(pre, lhsExpr, lNode);
		BooleanExpression tt = getExpressionManager().tt();
		if (validAccess.equals(tt))
			return;

		BooleanExpression assumption = stateToBoolean(pre);
		BooleanExpression assertion = assumption.implies(validAccess);
		pre.addAssertion(Identifiers.VALID_DEREF, assertion);
	}

	@Override
	public void setValidAccessRange(StateExpression pre, Expression lhsExpr,
			Expression sizeExpr, Node lNode) {
		if (!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK))
			return;
		BooleanExpression validAccessRange = validAccessRange(pre, lhsExpr,
				sizeExpr, lNode);
		BooleanExpression tt = getExpressionManager().tt();
		if (validAccessRange.equals(tt))
			return;

		BooleanExpression assumption = stateToBoolean(pre);
		BooleanExpression assertion = assumption.implies(validAccessRange);
		pre.addAssertion(Identifiers.VALID_DEREF, assertion);
	}

	@Override
	public void setValidFree(StateExpression pre, Expression regionExpr,
			Node ptrNode) {
		if (!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK))
			return;
		BooleanExpression validFree = applyValidFree(pre, regionExpr, ptrNode);
		BooleanExpression tt = getExpressionManager().tt();
		if (validFree.equals(tt))
			return;

		BooleanExpression assumption = stateToBoolean(pre);
		BooleanExpression assertion = assumption.implies(validFree);
		pre.addAssertion(Identifiers.VALID_FREE, assertion);
	}

	@Override
	public final BooleanExpression stateToBoolean(StateExpression state) {
		BooleanExpression memorySafe = getDisjointAssumption(state);
		BooleanExpression res = memorySafe;

		Expression guard = state.getGuard().simplify();
		if (guard != null)
			res = res.and(guard);

		BooleanExpression pc = state.getConstraint();
		if (pc != null)
			res = res.and(pc);

		return res;
	}

	/**
	 * Get the size of the region that <code>ptr</code> points-to from
	 * <code>state</code>
	 * 
	 * @param state
	 * @param ptr
	 * @param ptrNode
	 * @return
	 */
	protected abstract Expression getSizeOfRegion(StateExpression state,
			Expression region, Node ptrNode);

	protected abstract void substState(StateExpression state,
			Collection<? extends Expression> fromElems,
			Collection<? extends Expression> toElems);

	protected abstract void substSafetyPredicates(StateExpression state,
			Collection<? extends Expression> fromElems,
			Collection<? extends Expression> toElems);

	/**
	 * Update the memory safety predicates registered in the predicate map of
	 * <code>cleanState</code>, as "valid_access label_2", with the corresponding
	 * updated predicate function in <code>preState</code>, and apply it to
	 * "label_2"
	 * 
	 * @param cleanState
	 * @param preState
	 * @param fromPredicates
	 * @param toPredicates
	 * @return
	 */
	protected abstract void getSubstPredicatesPair(StateExpression cleanState,
			StateExpression preState, Collection<Expression> fromPredicates,
			Collection<Expression> toPredicates);

	/**
	 * Get the substitution element expressions pair from <code>fromState</code>
	 * and <code>toState</code>, and make sure if element pair are same, do not
	 * add them in.
	 * 
	 * @param fromState
	 * @param toState
	 * @param fromElems
	 * @param toElems
	 * @return
	 */
	protected abstract void getSubstElemsPair(StateExpression fromState,
			StateExpression toState, Collection<Expression> fromElems,
			Collection<Expression> toElems);

	abstract protected void propagateMemSafetyPredicates(StateExpression stateArg,
			StateExpression cleanState);

	abstract protected StateExpression joinPreStates(
			Iterable<StateExpression> preStates,
			Iterable<BooleanExpression> preGuards);

	abstract protected void updateMemState(StateExpression state,
			Expression index, Node idxNode, Expression value, @Nullable Node valNode);

	abstract protected void updateSizeStateWithFree(StateExpression state,
			Expression region, Expression sizeVal, Node ptrNode);

	abstract protected void updateMarkState(StateExpression state,
			Expression region, BooleanExpression mark, Node ptrNode);

	/**
	 * Update the size array in <code>state</code> with <code>
	 * sizeArr[region] := size</code>.
	 * 
	 * @param state
	 * @param region
	 * @param size
	 * @param ptrNode
	 *          is only useful in multi-state
	 * @return
	 */
	protected abstract void updateSizeStateWithAlloc(StateExpression state,
			Expression region, Expression size, Node ptrNode);

	abstract protected Expression dereference(StateExpression state,
			Expression index, Node idxNode);

	abstract protected BooleanExpression getDisjointAssumption(
			StateExpression state);

	ExpressionManager getExpressionManager() {
		return encoding.getExpressionManager();
	}

	BooleanExpression joinConstraints(
			Iterable<? extends StateExpression> preStates) {
		Multimap<Expression, BooleanExpression> guardPCMap = LinkedHashMultimap
				.create();
		for (StateExpression preState : preStates) {
			if (preState.getConstraint() == null)
				continue;
			guardPCMap.put(preState.getConstraint(), preState.getGuard());
		}

		if (guardPCMap.isEmpty())
			return null;
		if (guardPCMap.size() < Iterables.size(preStates))
			return getITEExpressionWithDefaultValue(guardPCMap, encoding.tt())
					.asBooleanExpression();
		else
			return getITEExpression(guardPCMap).asBooleanExpression();
	}

	void joinMemTrackers(StateExpression joinState,
			Iterable<? extends StateExpression> preStates) {
		if (!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK))
			return;

		Multimap<Expression, BooleanExpression> guardRegionSizeTrackerMap = LinkedHashMultimap
				.create();
		for (StateExpression preState : preStates) {
			Expression regionSizeTracker = preState.getMemTracker();
			guardRegionSizeTrackerMap.put(regionSizeTracker, preState.getGuard());
		}

		if (guardRegionSizeTrackerMap.isEmpty())
			return;

		Expression joinMemTracker;
		if (guardRegionSizeTrackerMap.size() < Iterables.size(preStates))
			joinMemTracker = getITEExpressionWithDefaultValue(
					guardRegionSizeTrackerMap, formatter.getSizeZero());
		else
			joinMemTracker = getITEExpression(guardRegionSizeTrackerMap);

		joinState.setMemTracker(joinMemTracker);
	}

	BooleanExpression joinGuards(Iterable<? extends StateExpression> preStates) {
		Iterable<BooleanExpression> guards = Iterables.transform(preStates,
				pickGuard);
		return encoding.or(guards).asBooleanExpression();
	}

	VariableExpression createFreshRegion() {
		String regionName = Identifiers.uniquify(REGION_VARIABLE_NAME);
		return formatter.getFreshPtr(regionName, false).asVariable();
	}

	Expression getITEExpression(
			Multimap<Expression, BooleanExpression> guardHoareMap) {
		// Check if all the cases are same, then just return the case
		Collection<Expression> caseSet = guardHoareMap.keySet();
		if (caseSet.size() == 1)
			return caseSet.iterator().next();

		Expression resExpr = null;
		for (Expression currCase : caseSet) {
			if (resExpr == null) {
				resExpr = currCase;
			} else {
				BooleanExpression guard = getExpressionManager()
						.or(guardHoareMap.get(currCase));
				resExpr = guard.ifThenElse(currCase, resExpr);
			}
		}

		return resExpr;
	}

	Expression getITEExpressionWithDefaultValue(
			Multimap<Expression, BooleanExpression> guardHoareMap,
			final Expression defaultCase) {
		Preconditions.checkNotNull(defaultCase);
		Collection<Expression> caseSet = guardHoareMap.keySet();

		if (caseSet.size() == 1 && defaultCase.equals(caseSet.iterator().next()))
			return defaultCase;

		Expression resExpr = defaultCase;
		for (Expression currCase : caseSet) {
			BooleanExpression guard = getExpressionManager()
					.or(guardHoareMap.get(currCase));
			assert (currCase.getType().equals(resExpr.getType()));
			resExpr = guard.ifThenElse(currCase, resExpr);
		}

		return resExpr;
	}

	void plusRegionSize(StateExpression state, Expression size) {
		if (!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK))
			return;

		Expression memTracker = state.getMemTracker();
		size = formatter.castToSize(size);
		memTracker = encoding.plus(memTracker, size);
		state.setMemTracker(memTracker);
	}

	void minusRegionSize(StateExpression state, Expression region, Node ptrNode) {
		if (!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK))
			return;
		if (Preferences.isSet(Preferences.OPTION_TWOROUND_MEMCHECK)) {
			if (Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
				Expression size = getSizeOfRegion(state, region, ptrNode);
				state.addConstraint(
						encoding.neq(size, formatter.getSizeZero()).asBooleanExpression());
			}
		}

		Expression size = getSizeOfRegion(state, region, ptrNode);
		Expression regionSizeTracker = state.getMemTracker();
		regionSizeTracker = encoding.minus(regionSizeTracker, size);
		state.setMemTracker(regionSizeTracker);
	}

	void substMemTracker(StateExpression state,
			Collection<? extends Expression> fromElems,
			Collection<? extends Expression> toElems) {
		if (!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK))
			return;
		Expression memTracker = state.getMemTracker();
		Expression memTrackerPrime = memTracker.subst(fromElems, toElems);
		state.setMemTracker(memTrackerPrime);
	}

	void substConstraintGuard(StateExpression state,
			Collection<? extends Expression> fromElems,
			Collection<? extends Expression> toElems) {
		if (fromElems.isEmpty())
			return;

		if (state.getGuard() != null) { /* Substitute guards */
			BooleanExpression guard = state.getGuard();
			BooleanExpression guardPrime = guard.subst(fromElems, toElems)
					.asBooleanExpression();
			state.setGuard(guardPrime);
		}

		if (state.getConstraint() != null) { /* Substitute constraint */
			BooleanExpression pc = state.getConstraint();
			BooleanExpression pcPrime = pc.subst(fromElems, toElems)
					.asBooleanExpression();
			state.setConstraint(pcPrime);
		}
	}

	void substAssertions(StateExpression state,
			Collection<? extends Expression> fromElems,
			Collection<? extends Expression> toElems) {
		if (fromElems.isEmpty())
			return;

		Multimap<String, BooleanExpression> assertions = state.getAssertions();
		for (Entry<String, BooleanExpression> entry : ImmutableList
				.copyOf(assertions.entries())) {
			BooleanExpression assertion = entry.getValue();
			BooleanExpression assertionPrime = assertion.subst(fromElems, toElems)
					.asBooleanExpression();
			assertions.remove(entry.getKey(), assertion);
			assertions.put(entry.getKey(), assertionPrime);
		}
	}

	void substPredicatesConstraint(StateExpression state,
			Collection<Expression> fromPredicates,
			Collection<Expression> toPredicates) {
		if (fromPredicates.isEmpty())
			return;
		if (state.getConstraint() == null)
			return;

		BooleanExpression pc = state.getConstraint();
		BooleanExpression pcPrime = pc.subst(fromPredicates, toPredicates)
				.asBooleanExpression();
		state.setConstraint(pcPrime);
	}

	void propagateMemTracker(StateExpression fromState, StateExpression toState) {
		if (!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK))
			return;
		Expression fromMemTracker = fromState.getMemTracker();
		Expression toMemTracker = toState.getMemTracker();
		toState.setMemTracker(encoding.plus(fromMemTracker, toMemTracker));
	}

	/**
	 * Propagate the new labels in <code>fromState</code> which are not in the
	 * <code>
	 * toState</code> into the <code>toState</code>
	 * 
	 * @param fromState
	 * @param toState
	 */
	void propagateNewSubState(StateExpression fromState,
			StateExpression toState) {
		if (fromState.isLambda()) {
			Map<String, SingleLambdaStateExpression> fromMap = fromState
					.asMultiLambda().getStateMap();
			Map<String, SingleLambdaStateExpression> toMap = toState.asMultiLambda()
					.getStateMap();

			Collection<String> newSubStateNames = Sets.newHashSet(fromMap.keySet());
			newSubStateNames.removeAll(toMap.keySet());

			if (newSubStateNames.isEmpty())
				return;

			for (String label : newSubStateNames) {
				toMap.put(label, fromMap.get(label));
			}
		} else {
			Map<String, SingleStateExpression> fromMap = fromState.asMultiple()
					.getStateMap();
			Map<String, SingleStateExpression> toMap = toState.asMultiple()
					.getStateMap();

			Collection<String> newSubStateNames = Sets.newHashSet(fromMap.keySet());
			newSubStateNames.removeAll(toMap.keySet());

			if (newSubStateNames.isEmpty())
				return;

			for (String label : newSubStateNames) {
				toMap.put(label, fromMap.get(label));
			}
		}
	}

	void propagateAssertions(StateExpression stateArg,
			StateExpression cleanState) {
		BooleanExpression assumption = stateToBoolean(stateArg);

		Multimap<String, BooleanExpression> assertions = cleanState.getAssertions();
		for (Entry<String, BooleanExpression> entry : ImmutableList
				.copyOf(assertions.entries())) {
			BooleanExpression assertion = entry.getValue();
			BooleanExpression assertionPrime = assumption.implies(assertion);
			assertions.remove(entry.getKey(), assertion);
			assertions.put(entry.getKey(), assertionPrime);
		}
	}
}
