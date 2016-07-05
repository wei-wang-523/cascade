package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.annotation.Nullable;

import xtc.tree.Node;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.inject.Inject;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.safety.IRMemSafetyEncoding;
import edu.nyu.cascade.ir.memory.safety.PredicateClosure;
import edu.nyu.cascade.ir.pass.IRAliasAnalyzer;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;

public class SingleLambdaStateFactory<T> extends AbstractStateFactory<T> {

	private final IRMemSafetyEncoding memSafetyEncoding;
	private final SingleStateFactory<T> singleStateFactory;

	@Inject
	SingleLambdaStateFactory(ExpressionEncoding encoding,
			IRDataFormatter formatter, IRMemSafetyEncoding memSafetyEncoding) {
		super(encoding, formatter);
		this.memSafetyEncoding = memSafetyEncoding;
		this.singleStateFactory = createSingle(encoding, formatter);
	}

	@Override
	public void reset() {
	}

	@Override
	public <X> void setLabelAnalyzer(IRAliasAnalyzer<X> preprocessor) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void malloc(StateExpression state, Expression ptr, Expression size,
			Node ptrNode) {
		ExpressionEncoding encoding = getExpressionEncoding();
		VariableExpression region = createFreshRegion();
		state.addRegion(region);
		BooleanExpression tt = encoding.tt().asBooleanExpression();

		updateMemState(state, ptr, ptrNode, region, null);
		updateSizeStateWithAlloc(state, region, size, ptrNode);
		updateMarkState(state, region, tt, ptrNode);

		plusRegionSize(state, size);
		state.addConstraint(applyValidMalloc(state, region, size, ptrNode));
	}

	@Override
	public void calloc(StateExpression state, Expression ptr, Expression nitem,
			Expression size, Node ptrNode) {
		ExpressionEncoding encoding = getExpressionEncoding();
		Expression multSize = encoding.times(nitem, size);
		VariableExpression region = createFreshRegion();
		state.addRegion(region);
		BooleanExpression tt = encoding.tt().asBooleanExpression();

		updateMemState(state, ptr, ptrNode, region, null);
		updateSizeStateWithAlloc(state, region, multSize, ptrNode);
		updateMarkState(state, region, tt, ptrNode);

		plusRegionSize(state, multSize);
		state.addConstraint(applyValidMalloc(state, region, multSize, ptrNode));
		state.addConstraint(applyMemset(state, region, multSize,
				getExpressionEncoding().characterConstant(0), ptrNode));
	}

	@Override
	public void alloca(StateExpression state, Expression ptr, Expression size,
			Node ptrNode) {
		VariableExpression region = createFreshRegion();
		state.addRegion(region);
		updateMemState(state, ptr, ptrNode, region, null);
		updateSizeStateWithAlloc(state, region, size, ptrNode);
		state.addConstraint(applyValidMalloc(state, region, size, ptrNode));
	}

	@Override
	public SingleLambdaStateExpression resolvePhiNode(
			Collection<StateExpression> preStates) {
		/* Build the joined state */
		Iterable<BooleanExpression> preGuards = Iterables.transform(preStates,
				pickGuard);
		SingleLambdaStateExpression joinState = joinPreStates(preStates, preGuards);

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
	public BooleanExpression applyValidMalloc(StateExpression state,
			Expression ptr, Expression size, Node ptrNode) {
		return memSafetyEncoding.validMalloc(ptr, size);
	}

	@Override
	public BooleanExpression applyMemset(StateExpression state, Expression region,
			Expression size, Expression value, Node ptrNode) {
		return singleStateFactory.applyMemset(state.asSingleLambda()
				.getSingleState(), region, size, value, ptrNode);
	}

	@Override
	public BooleanExpression applyMemset(StateExpression state, Expression region,
			Expression size, int value, Node ptrNode) {
		return singleStateFactory.applyMemset(state.asSingleLambda()
				.getSingleState(), region, size, value, ptrNode);
	}

	@Override
	public BooleanExpression applyMemcpy(StateExpression state,
			Expression destRegion, Expression srcRegion, Expression size,
			Node destNode, Node srcNode) {
		return singleStateFactory.applyMemcpy(state.asSingleLambda()
				.getSingleState(), destRegion, srcRegion, size, destNode, srcNode);
	}

	@Override
	public BooleanExpression applyValidFree(StateExpression state, Expression ptr,
			Node ptrNode) {
		ArrayExpression markArr = state.asSingleLambda().getSingleState().getMark();
		return memSafetyEncoding.validFree(markArr, ptr);
	}

	@Override
	public BooleanExpression validAccess(StateExpression state, Expression ptr,
			Node ptrNode) {
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
		PredicateClosure func = memSafetyEncoding.getValidAccess(lambdaState);
		lambdaState.registerPredicate(func.getUninterpretedFunc(), ptr);
		return func.eval(ptr).asBooleanExpression();
	}

	@Override
	public BooleanExpression validAccessRange(StateExpression state,
			Expression ptr, Expression size, Node ptrNode) {
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
		PredicateClosure func = memSafetyEncoding.getValidAccessRange(lambdaState);
		size = getDataFormatter().castToSize(size);
		lambdaState.registerPredicate(func.getUninterpretedFunc(), ptr, size);
		return func.eval(ptr, size).asBooleanExpression();
	}

	@Override
	public SingleLambdaStateExpression freshState() {
		SingleLambdaStateExpression lambdaState = SingleLambdaStateExpression
				.create(singleStateFactory.freshSingleState());
		memSafetyEncoding.initMemSafetyPredicates(lambdaState);
		lambdaState.setMemTracker(getDataFormatter().getSizeZero());
		return lambdaState;
	}

	@Override
	public void addStackVar(StateExpression state, Expression lval,
			IRVarInfo info) {
		if (!info.isStatic())
			state.addVar(lval.asVariable());
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
		xtc.type.Type lvalType = info.getXtcType();
		long size = getCTypeAnalyzer().getSize(lvalType);
		Expression lvalSize = getExpressionEncoding().integerConstant(size);
		addStackVar(lambdaState, lval, lvalSize);
	}

	@Override
	public void addStackArray(StateExpression state, Expression lval,
			Expression rval, IRVarInfo info, Node sourceNode) {
		if (!info.isStatic())
			state.addVar(lval.asVariable());
		updateSizeStateWithAlloc(state, lval, rval, sourceNode);
		state.addConstraint(applyValidMalloc(state, lval, rval, sourceNode));
	}

	@Override
	public Expression lookupSize(StateExpression state, Expression ptr,
			Node node) {
		ArrayExpression sizeArr = state.asSingleLambda().getSingleState().getSize();
		return getDataFormatter().indexSizeArray(sizeArr, ptr);
	}

	@Override
	public void propagateState(StateExpression cleanState,
			StateExpression stateArg) {
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
	}

	/** Shallow copy */
	@Override
	public SingleLambdaStateExpression copy(StateExpression state) {
		SingleLambdaStateExpression singleLambdaState = state.asSingleLambda();
		SingleStateExpression singleState = singleLambdaState.getSingleState();
		SingleStateExpression singleStateCopy = singleStateFactory.copy(
				singleState);
		SingleLambdaStateExpression newState = SingleLambdaStateExpression.create(
				singleStateCopy);

		newState.setConstraint(state.getConstraint());
		newState.setGuard(state.getGuard());
		newState.putAllPredicateMap(singleLambdaState.getPredicateMap());
		newState.putAllSafetyPredicateClosures(singleLambdaState
				.getSafetyPredicateClosures());
		newState.putAllSafetyPredicates(singleLambdaState.getSafetyPredicates());
		newState.addVars(state.getVars());
		newState.addRegions(state.getRegions());
		newState.setAssertions(state.getAssertions());
		newState.setMemTracker(state.getMemTracker());
		return newState;
	}

	@Override
	public void substitute(StateExpression state,
			Collection<? extends Expression> vars,
			Collection<? extends Expression> freshVars) {
		substState(state, vars, freshVars);
		substConstraintGuard(state, vars, freshVars);
		substSafetyPredicates(state, vars, freshVars);
		substAssertions(state, vars, freshVars);
		substMemTracker(state, vars, freshVars);
	}

	@Override
	public Collection<BooleanExpression> getAssumptions() {
		return memSafetyEncoding.getAssumptions();
	}

	@Override
	protected BooleanExpression getDisjointAssumption(StateExpression state) {
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
		return memSafetyEncoding.getPreDisjoint(lambdaState);
	}

	@Override
	protected Expression getSizeOfRegion(StateExpression state, Expression region,
			Node ptrNode) {
		SingleStateExpression singleState = state.asSingleLambda().getSingleState();
		ArrayExpression sizeArr = singleState.getSize();
		return getDataFormatter().indexSizeArray(sizeArr, region);
	}

	@Override
	protected void updateMemState(StateExpression state, Expression index,
			Node idxNode, Expression value, @Nullable Node valNode) {
		SingleStateExpression singleState = state.asSingleLambda().getSingleState();
		singleStateFactory.updateMemState(singleState, index, idxNode, value,
				valNode);
	}

	@Override
	protected void updateSizeStateWithFree(StateExpression state,
			Expression region, Expression size, Node ptrNode) {
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
		deleteHeapRegInfo(lambdaState, region);
		SingleStateExpression singleState = lambdaState.getSingleState();
		singleStateFactory.updateSizeStateWithFree(singleState, region, size,
				ptrNode);
	}

	@Override
	protected void updateMarkState(StateExpression state, Expression region,
			BooleanExpression mark, Node ptrNode) {
		SingleStateExpression singleState = state.asSingleLambda().getSingleState();
		singleStateFactory.updateMarkState(singleState, region, mark, ptrNode);
	}

	/** <code>ptr</code> is not used here */
	@Override
	protected void updateSizeStateWithAlloc(StateExpression state,
			Expression region, Expression size, Node ptrNode) {
		SingleLambdaStateExpression lambdaState = state.asSingleLambda();
		SingleStateExpression singleState = lambdaState.getSingleState();
		singleStateFactory.updateSizeStateWithFree(singleState, region, size,
				ptrNode);
		addHeapRegInfo(lambdaState, region);
	}

	@Override
	protected void propagateMemSafetyPredicates(StateExpression stateArg,
			StateExpression cleanState) {
		memSafetyEncoding.propagateSafetyPredicates(stateArg.asSingleLambda(),
				cleanState.asSingleLambda());
	}

	@Override
	protected void substState(StateExpression state,
			Collection<? extends Expression> fromElems,
			Collection<? extends Expression> toElems) {
		SingleStateExpression singleState = state.asSingleLambda().getSingleState();
		singleStateFactory.substState(singleState, fromElems, toElems);
	}

	@Override
	protected void getSubstPredicatesPair(StateExpression cleanState,
			StateExpression preState, Collection<Expression> fromPredicates,
			Collection<Expression> toPredicates) {

		// FIXME: may don't need for memory and size array, only needs to update for
		// constraint
		Multimap<Expression, Collection<Expression>> cleanPredicateMap = cleanState
				.asSingleLambda().getPredicateMap();

		SingleLambdaStateExpression preLambdaState = preState.asSingleLambda();

		for (Entry<Expression, Collection<Expression>> entry : cleanPredicateMap
				.entries()) {
			FunctionExpression predicate = entry.getKey().asFunctionExpression();
			Collection<Expression> args = entry.getValue();
			Expression fromExpr = predicate.apply(args);
			Expression toExpr = memSafetyEncoding.applyUpdatedPredicate(
					preLambdaState, predicate, args);

			if (!fromExpr.equals(toExpr)) {
				fromPredicates.add(fromExpr);
				toPredicates.add(toExpr);
			}
		}
	}

	@Override
	protected void getSubstElemsPair(StateExpression fromState,
			StateExpression toState, Collection<Expression> fromElems,
			Collection<Expression> toElems) {
		singleStateFactory.getSubstElemsPair(fromState.asSingleLambda()
				.getSingleState(), toState.asSingleLambda().getSingleState(), fromElems,
				toElems);
	}

	@Override
	protected SingleLambdaStateExpression joinPreStates(
			Iterable<StateExpression> preStates,
			Iterable<BooleanExpression> preGuards) {
		int preStateSize = Iterables.size(preStates);

		Collection<StateExpression> preSingleStates = Lists
				.newArrayListWithCapacity(preStateSize);
		for (StateExpression preState : preStates) {
			preSingleStates.add(preState.asSingleLambda().getSingleState());
		}

		SingleStateExpression joinState = singleStateFactory.joinPreStates(
				preSingleStates, preGuards);
		SingleLambdaStateExpression joinLambdaState = SingleLambdaStateExpression
				.create(joinState);

		memSafetyEncoding.initMemSafetyPredicates(joinLambdaState);

		// Create join state predicates
		joinSafetyProperties(preStates, preGuards, joinLambdaState);

		return joinLambdaState;
	}

	@Override
	protected Expression dereference(StateExpression state, Expression index,
			Node indexNode) {
		ArrayExpression memArr = state.asSingleLambda().getSingleState()
				.getMemory();
		xtc.type.Type idxType = CType.getType(indexNode);
		return getDataFormatter().indexMemoryArray(memArr, index, idxType);
	}

	@Override
	protected void substSafetyPredicates(StateExpression state,
			Collection<? extends Expression> fromElems,
			Collection<? extends Expression> toElems) {
		SingleLambdaStateExpression singleLambdaState = state.asSingleLambda();

		Multimap<Expression, Collection<Expression>> predicateMap = singleLambdaState
				.getPredicateMap();
		for (Entry<Expression, Collection<Expression>> entry : ImmutableList.copyOf(
				predicateMap.entries())) {
			Collection<Expression> values = entry.getValue();
			if (values.isEmpty())
				continue;

			predicateMap.remove(entry.getKey(), values);
			Collection<Expression> valuesPrime = Lists.newArrayListWithCapacity(values
					.size());
			for (Expression value : values)
				valuesPrime.add(value.subst(fromElems, toElems));
			predicateMap.put(entry.getKey(), valuesPrime);
		}

		Map<String, BooleanExpression> safetyPredicates = singleLambdaState
				.getSafetyPredicates();
		for (String label : ImmutableSet.copyOf(safetyPredicates.keySet())) {
			BooleanExpression safetyPredicate = safetyPredicates.get(label);
			BooleanExpression safetyPredicatePrime = safetyPredicate.subst(fromElems,
					toElems).asBooleanExpression();
			safetyPredicates.put(label, safetyPredicatePrime);
		}

		Map<String, PredicateClosure> safetyPredicateClosures = singleLambdaState
				.getSafetyPredicateClosures();
		for (String label : ImmutableSet.copyOf(safetyPredicateClosures.keySet())) {
			PredicateClosure safetyPredicateClosure = safetyPredicateClosures.get(
					label);
			Expression body = safetyPredicateClosure.getBodyExpr();
			Expression bodyPrime = body.subst(fromElems, toElems);
			PredicateClosure safetyPredicateClosurePrime = memSafetyEncoding.suspend(
					safetyPredicateClosure.getUninterpretedFunc(), bodyPrime,
					safetyPredicateClosure.getVars());
			safetyPredicateClosures.put(label, safetyPredicateClosurePrime);
		}
	}

	void addStackVar(SingleLambdaStateExpression lambdaState,
			Expression stVarExpr, Expression stVarSize) {
		memSafetyEncoding.updateStackMemSafetyPredicates(lambdaState, stVarExpr,
				stVarSize);
	}

	void addHeapRegInfo(SingleLambdaStateExpression lambdaState,
			Expression hpRegExpr) {
		ArrayExpression sizeArr = lambdaState.getSingleState().getSize();
		Expression hpRegSize = getDataFormatter().indexSizeArray(sizeArr,
				hpRegExpr);
		memSafetyEncoding.updateHeapMemSafetyPredicates(lambdaState, hpRegExpr,
				hpRegSize);
	}

	void deleteHeapRegInfo(SingleLambdaStateExpression lambdaState,
			Expression hpRegExpr) {
		ArrayExpression sizeArr = lambdaState.getSingleState().getSize();
		Expression hpRegSize = getDataFormatter().indexSizeArray(sizeArr,
				hpRegExpr);
		memSafetyEncoding.freeUpdateHeapMemSafetyPredicates(lambdaState, hpRegExpr,
				hpRegSize);
	}

	/**
	 * Create a single state expression with <code>name</code> and value type
	 * <code>type</code> as memory state element type, and initialize all the
	 * safety predicates
	 * 
	 * @param name
	 * @param type
	 * @return
	 */
	SingleLambdaStateExpression freshSingleLambdaState(String name, long width) {
		SingleLambdaStateExpression fresh = SingleLambdaStateExpression.create(
				singleStateFactory.freshSingleState(name, width));
		memSafetyEncoding.initMemSafetyPredicates(fresh);
		return fresh;
	}

	SingleLambdaStateExpression freshSingleLambdaState(String elemName,
			ArrayType[] elemTypes) {
		SingleLambdaStateExpression fresh = SingleLambdaStateExpression.create(
				singleStateFactory.freshSingleState(elemName, elemTypes));
		memSafetyEncoding.initMemSafetyPredicates(fresh);
		return fresh;
	}

	/**
	 * Create a single state expression with <code>name</code> and value type
	 * <code>type</code> as memory state element type, without initializing safety
	 * predicates
	 * 
	 * @param name
	 * @param elems
	 * @return
	 */
	SingleLambdaStateExpression createSingleLambdaState(String name,
			Expression mem, Expression size, Expression mark) {
		SingleLambdaStateExpression fresh = SingleLambdaStateExpression.create(
				SingleStateExpression.create(name, mem.asArray(), size.asArray(), mark
						.asArray()));
		return fresh;
	}

	void updateStructInMemState(SingleLambdaStateExpression state,
			Expression index, Expression value, long range) {
		SingleStateExpression singleState = state.getSingleState();
		singleStateFactory.updateStructInMemState(singleState, index, value, range);
	}

	private void joinSafetyProperties(Iterable<StateExpression> preStates,
			Iterable<BooleanExpression> preGuards,
			SingleLambdaStateExpression joinState) {
		ExpressionEncoding encoding = getExpressionEncoding();

		Collection<String> closurePropNames = memSafetyEncoding
				.getClosurePropNames();

		for (String name : closurePropNames) {
			Function<StateExpression, PredicateClosure> funcClosure = getFuncClosure(
					name);
			Iterable<PredicateClosure> preElems = Iterables.transform(preStates,
					funcClosure);
			PredicateClosure joinPreElems = getITEPredClosure(encoding, preElems,
					preGuards);
			joinState.putSafetyPredicateClosure(name, joinPreElems);
		}

		Collection<String> exprPropNames = memSafetyEncoding.getExprPropNames();

		for (String name : exprPropNames) {
			Function<StateExpression, BooleanExpression> func = getFuncExpr(name);
			Iterable<BooleanExpression> preElems = Iterables.transform(preStates,
					func);
			BooleanExpression joinPreElems = getITEPredicate(encoding, preElems,
					preGuards).asBooleanExpression();
			joinState.putSafetyPredicate(name, joinPreElems);
		}

		for (StateExpression preState : preStates) { // Combine predicate map
			joinState.putAllPredicateMap(preState.asSingleLambda().getPredicateMap());
		}

	}

	private BooleanExpression getITEPredicate(ExpressionEncoding encoding,
			Iterable<? extends Expression> exprs,
			Iterable<? extends Expression> guards) {
		Preconditions.checkArgument(Iterables.size(exprs) == Iterables.size(
				guards));

		Iterator<? extends Expression> itr = exprs.iterator();
		Iterator<? extends Expression> guardItr = guards.iterator();

		Expression resExpr = null;

		if (itr.hasNext()) {
			resExpr = itr.next();
			guardItr.next(); // the first case is the default case
		}

		ExpressionManager exprManager = encoding.getExpressionManager();
		while (itr.hasNext() && guardItr.hasNext()) {
			BooleanExpression guard = guardItr.next().asBooleanExpression();
			Expression currCase = itr.next();
			resExpr = exprManager.ifThenElse(guard, currCase, resExpr);
		}
		return resExpr.asBooleanExpression();
	}

	private PredicateClosure getITEPredClosure(ExpressionEncoding encoding,
			Iterable<? extends PredicateClosure> preClosures,
			Iterable<? extends Expression> guards) {
		Preconditions.checkArgument(Iterables.size(preClosures) == Iterables.size(
				guards));

		Iterator<? extends PredicateClosure> itr = preClosures.iterator();
		Iterator<? extends Expression> guardItr = guards.iterator();

		Expression resBodyExpr = null;
		Expression[] resVarExprs = null;
		List<Expression> unInterFunc = Lists.newArrayListWithCapacity(Iterables
				.size(preClosures));

		if (itr.hasNext()) {
			PredicateClosure preClosure = itr.next();
			resBodyExpr = preClosure.getBodyExpr();
			resVarExprs = preClosure.getVars();
			unInterFunc.add(preClosure.getUninterpretedFunc());
			guardItr.next(); // the first case is the default case
		}

		ExpressionManager exprManager = encoding.getExpressionManager();
		while (itr.hasNext() && guardItr.hasNext()) {
			BooleanExpression guard = guardItr.next().asBooleanExpression();
			PredicateClosure preClosure = itr.next();
			Expression currCase = preClosure.eval(resVarExprs); // TODO: may removed
																													// for non-unique
																													// variable creating
			resBodyExpr = exprManager.ifThenElse(guard, currCase, resBodyExpr);
			unInterFunc.add(preClosure.getUninterpretedFunc());
		}

		final Expression firstFunc = unInterFunc.get(0);

		// assert(Iterables.all(unInterFunc, new Predicate<Expression>(){
		// @Override
		// public boolean apply(Expression expr) {
		// return expr.equals(firstFunc);
		// }
		// }));

		return memSafetyEncoding.suspend(firstFunc, resBodyExpr, resVarExprs);
	}

	private static Function<StateExpression, BooleanExpression> getFuncExpr(
			final String name) {
		return new Function<StateExpression, BooleanExpression>() {
			@Override
			public BooleanExpression apply(StateExpression state) {
				return state.asSingleLambda().getSafetyPredicate(name);
			}
		};
	}

	private static Function<StateExpression, PredicateClosure> getFuncClosure(
			final String name) {
		return new Function<StateExpression, PredicateClosure>() {
			@Override
			public PredicateClosure apply(StateExpression state) {
				return state.asSingleLambda().getSafetyPredicateClosure(name);
			}
		};
	}
}
