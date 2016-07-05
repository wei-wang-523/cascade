package edu.nyu.cascade.ir.memory.safety;

import java.util.Collection;
import java.util.Collections;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.safety.AbstractStmtMemSafetyEncoding.SafetyPredicate.Kind;
import edu.nyu.cascade.ir.state.SingleLambdaStateExpression;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class SoundStmtLinearMemSafetyEncoding extends
		AbstractStmtMemSafetyEncoding {

	private final static Collection<String> FUN_NAMES = Lists.newArrayList(
			SafetyPredicate.Kind.VALID_ACCESS_RANGE.name(),
			SafetyPredicate.Kind.VALID_ACCESS.name(), SafetyPredicate.Kind.DISJOINT
					.name());
	private final static Collection<String> FUN_DISJOINT_NAMES = Lists
			.newArrayList(SafetyPredicate.Kind.DISJOINT.name());
	private final static Collection<String> PRED_NAMES = Collections.singleton(
			SafetyPredicate.Kind.PRE_DISJOINT.name());

	private final Expression ptrVar, sizeVar;

	private SoundStmtLinearMemSafetyEncoding(ExpressionEncoding encoding,
			IRDataFormatter formatter) {
		super(encoding, formatter);
		ExpressionManager exprManager = encoding.getExpressionManager();
		ptrVar = exprManager.variable(ptrVarName, formatter.getAddressType(), true);
		sizeVar = exprManager.variable(sizeVarName, formatter.getSizeType(), true);
	}

	public static SoundStmtLinearMemSafetyEncoding create(
			ExpressionEncoding encoding, IRDataFormatter formatter) {
		return new SoundStmtLinearMemSafetyEncoding(encoding, formatter);
	}

	@Override
	public void initMemSafetyPredicates(SingleLambdaStateExpression state) {
		if (Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			initSafetyPredicate(Kind.VALID_ACCESS, state, ptrVar, sizeVar);
			initSafetyPredicate(Kind.VALID_ACCESS_RANGE, state, ptrVar, sizeVar);
		}
		initSafetyPredicate(Kind.DISJOINT, state, ptrVar, sizeVar);
		initSafetyPredicate(Kind.PRE_DISJOINT, state, ptrVar, sizeVar);
	}

	@Override
	public void updateHeapMemSafetyPredicates(SingleLambdaStateExpression state,
			Expression ptrExpr, Expression sizeExpr) {
		if (Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			updateHeapFunValidAccess(state, ptrExpr, sizeExpr);
			updateHeapFunValidAccessRange(state, ptrExpr, sizeExpr);
		}
		/* The order of pre-disjoint and fun-disjoint updates must be maintained */
		updateHeapPreDisjoint(state, ptrExpr, sizeExpr);
		updateHeapFunDisjoint(state, ptrExpr, sizeExpr);
	}

	@Override
	public void updateStackMemSafetyPredicates(SingleLambdaStateExpression state,
			Expression ptrExpr, Expression sizeExpr) {
		if (Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			updateStackFunValidAccess(state, ptrExpr, sizeExpr);
			updateStackFunValidAccessRange(state, ptrExpr, sizeExpr);
		}
		/* The order of pre-disjoint and fun-disjoint updates must be maintained */
		updateStackPreDisjoint(state, ptrExpr, sizeExpr);
		updateStackFunDisjoint(state, ptrExpr, sizeExpr);
	}

	@Override
	public BooleanExpression validMalloc(Expression region, Expression size) {
		Expression notOverflow = encoding.notOverflow(region, size);
		BooleanExpression notNull = region.neq(formatter.getNullAddress());
		return notNull.and(notOverflow);
		// Expression isNull = ptr.eq(formatter.getNullAddress());
		// /* size not overflow, but could be zero -- malloc(0) */
		// return encoding.or(isNull, notOverflow).asBooleanExpression();
	}

	@Override
	public BooleanExpression validFree(ArrayExpression markArr,
			Expression region) {
		Preconditions.checkArgument(markArr.getType().getIndexType().equals(
				formatter.getAddressType()));
		Preconditions.checkArgument(markArr.getType().getElementType().isBoolean());
		Preconditions.checkArgument(region.getType().equals(formatter
				.getAddressType()));

		BooleanExpression mark = markArr.index(region).asBooleanExpression();
		BooleanExpression tt = mark.getType().asBooleanType().tt();
		return mark.eq(tt);
	}

	@Override
	public Collection<String> getExprPropNames() {
		return PRED_NAMES;
	}

	@Override
	public Collection<String> getClosurePropNames() {
		return Preferences.isSet(Preferences.OPTION_MEMORY_CHECK) ? FUN_NAMES
				: FUN_DISJOINT_NAMES;
	}

	private void updateStackFunValidAccess(SingleLambdaStateExpression state,
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);

		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();

		assert (vars.length == 1);
		Expression bodyPrime = encoding.or(encoding.within(ptrExpr, sizeExpr,
				vars[0]), body);

		PredicateClosure closurePrime = suspend(func, bodyPrime, vars[0]);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}

	private void updateHeapFunValidAccess(SingleLambdaStateExpression state,
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);

		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();

		assert (vars.length == 1);
		Expression bodyPrime = encoding.or(encoding.and(ptrExpr.neq(formatter
				.getNullAddress()), sizeExpr.neq(formatter.getSizeZero()), encoding
						.within(ptrExpr, sizeExpr, vars[0])), body);

		PredicateClosure closurePrime = suspend(func, bodyPrime, vars[0]);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}

	private void updateStackFunValidAccessRange(SingleLambdaStateExpression state,
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);

		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();

		assert (vars.length == 2);
		Expression bodyPrime = encoding.or(encoding.within(ptrExpr, sizeExpr,
				vars[0], vars[1]), body);

		PredicateClosure closurePrime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}

	private void updateHeapFunValidAccessRange(SingleLambdaStateExpression state,
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);

		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();

		assert (vars.length == 2);
		Expression bodyPrime = encoding.or(encoding.and(ptrExpr.neq(formatter
				.getNullAddress()), sizeExpr.neq(formatter.getSizeZero()), encoding
						.within(ptrExpr, sizeExpr, vars[0], vars[1])), body);

		PredicateClosure closurePrime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}

	private void updateHeapFunDisjoint(SingleLambdaStateExpression state,
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.DISJOINT.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);

		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();

		assert (vars.length == 2);

		Expression bodyPrime = encoding.and(body, encoding.implies(ptrExpr.neq(
				formatter.getNullAddress()), encoding.ifThenElse(sizeExpr.neq(formatter
						.getSizeZero()), encoding.disjoint(vars[0], vars[1], ptrExpr,
								sizeExpr), encoding.disjoint(vars[0], vars[1], ptrExpr))));

		PredicateClosure closurePrime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}

	private void updateStackFunDisjoint(SingleLambdaStateExpression state,
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.DISJOINT.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);

		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();

		assert (vars.length == 2);
		Expression bodyPrime = encoding.and(body, encoding.disjoint(ptrExpr,
				sizeExpr, vars[0], vars[1]));

		PredicateClosure closurePrime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}

	private void updateStackPreDisjoint(SingleLambdaStateExpression state,
			Expression ptrExpr, Expression sizeExpr) {
		String disjointName = SafetyPredicate.Kind.DISJOINT.name();
		String preDisjointName = SafetyPredicate.Kind.PRE_DISJOINT.name();

		PredicateClosure disjoint_closure = state.getSafetyPredicateClosure(
				disjointName);
		BooleanExpression pre_disjoint = state.getSafetyPredicate(preDisjointName);

		BooleanExpression pre_disjoint_prime = encoding.and(pre_disjoint,
				disjoint_closure.eval(ptrExpr, sizeExpr), encoding.notOverflow(ptrExpr,
						sizeExpr), ptrExpr.neq(formatter.getNullAddress()))
				.asBooleanExpression();

		state.putSafetyPredicate(preDisjointName, pre_disjoint_prime);
		Expression func = disjoint_closure.getUninterpretedFunc();
		state.registerPredicate(func, ptrExpr, sizeExpr);
	}

	private void updateHeapPreDisjoint(SingleLambdaStateExpression state,
			Expression ptrExpr, Expression sizeExpr) {
		String disjointName = SafetyPredicate.Kind.DISJOINT.name();
		String preDisjointName = SafetyPredicate.Kind.PRE_DISJOINT.name();

		PredicateClosure disjoint_closure = state.getSafetyPredicateClosure(
				disjointName);
		BooleanExpression pre_disjoint = state.getSafetyPredicate(preDisjointName);

		/*
		 * Here, we miss the clause like:
		 * implies(ptr.neq(formatter.getNullAddress()),
		 * encoding.lessThanOrEqual(ptr, encoding.plus(ptr, size))) Because the
		 * valid_malloc(ptr, size) has already specify it as assumption
		 */
		BooleanExpression pre_disjoint_prime = encoding.and(pre_disjoint,
				disjoint_closure.eval(ptrExpr, sizeExpr)).asBooleanExpression();

		state.putSafetyPredicate(preDisjointName, pre_disjoint_prime);
		Expression func = disjoint_closure.getUninterpretedFunc();
		state.registerPredicate(func, ptrExpr, sizeExpr);
	}

	@Override
	public void freeUpdateHeapMemSafetyPredicates(
			SingleLambdaStateExpression state, Expression ptrExpr,
			Expression sizeExpr) {
		if (Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			updateHeapFunValidAccessFree(state, ptrExpr, sizeExpr);
			updateHeapFunValidAccessRangeFree(state, ptrExpr, sizeExpr);
		}
	}

	private void updateHeapFunValidAccessFree(SingleLambdaStateExpression state,
			Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);

		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();

		assert (vars.length == 1);
		Expression bodyPrime = encoding.and(body, encoding.not(encoding.within(
				ptrExpr, sizeExpr, vars[0])));

		PredicateClosure closurePrime = suspend(func, bodyPrime, vars[0]);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}

	private void updateHeapFunValidAccessRangeFree(
			SingleLambdaStateExpression state, Expression ptrExpr,
			Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure closure = state.getSafetyPredicateClosure(propName);

		Expression func = closure.getUninterpretedFunc();
		Expression body = closure.getBodyExpr();
		Expression[] vars = closure.getVars();

		assert (vars.length == 2);
		Expression bodyPrime = encoding.and(body, encoding.not(encoding.within(
				ptrExpr, sizeExpr, vars[0], vars[1])));

		PredicateClosure closurePrime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, closurePrime);
	}

}
