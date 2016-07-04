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

public class OrderStmtLinearMemSafetyEncoding extends
    AbstractStmtMemSafetyEncoding {

	private final static Collection<String> FUN_NAMES = Lists.newArrayList(
	    SafetyPredicate.Kind.VALID_ACCESS_RANGE.name(),
	    SafetyPredicate.Kind.VALID_ACCESS.name(),
	    SafetyPredicate.Kind.STACK_ORDERED.name(),
	    SafetyPredicate.Kind.HEAP_ORDERED.name());
	private final static Collection<String> FUN_ORDER_NAMES = Lists.newArrayList(
	    SafetyPredicate.Kind.STACK_ORDERED.name(),
	    SafetyPredicate.Kind.HEAP_ORDERED.name());
	private final static Collection<String> PRED_NAMES = Collections.singleton(
	    SafetyPredicate.Kind.PRE_DISJOINT.name());

	private final Expression ptrVar, sizeVar;

	private OrderStmtLinearMemSafetyEncoding(ExpressionEncoding encoding,
	    IRDataFormatter formatter) {
		super(encoding, formatter);
		ExpressionManager exprManager = encoding.getExpressionManager();
		ptrVar = exprManager.variable(ptrVarName, formatter.getAddressType(), true);
		sizeVar = exprManager.variable(sizeVarName, formatter.getSizeType(), true);
	}

	public static OrderStmtLinearMemSafetyEncoding create(
	    ExpressionEncoding encoding, IRDataFormatter formatter) {
		return new OrderStmtLinearMemSafetyEncoding(encoding, formatter);
	}

	@Override
	public BooleanExpression validMalloc(Expression ptr, Expression size) {
		Expression notOverflow = encoding.notOverflow(ptr, size);
		BooleanExpression notNull = ptr.neq(formatter.getNullAddress());
		return notNull.and(notOverflow);
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
	public void initMemSafetyPredicates(SingleLambdaStateExpression state) {
		if (Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) {
			initSafetyPredicate(Kind.VALID_ACCESS, state, ptrVar, sizeVar);
			initSafetyPredicate(Kind.VALID_ACCESS_RANGE, state, ptrVar, sizeVar);
		}
		initSafetyPredicate(Kind.STACK_ORDERED, state, ptrVar, sizeVar);
		initSafetyPredicate(Kind.HEAP_ORDERED, state, ptrVar, sizeVar);
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
		updateFunHeapOrdered(state, ptrExpr, sizeExpr);
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
		updateFunStackOrdred(state, ptrExpr);
	}

	@Override
	public Collection<String> getExprPropNames() {
		return PRED_NAMES;
	}

	@Override
	public Collection<String> getClosurePropNames() {
		return Preferences.isSet(Preferences.OPTION_MEMORY_CHECK) ? FUN_NAMES
		    : FUN_ORDER_NAMES;
	}

	private void updateStackFunValidAccess(SingleLambdaStateExpression state,
	    Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS.name();
		PredicateClosure valid_access_closure = state.getSafetyPredicateClosure(
		    propName);

		Expression func = valid_access_closure.getUninterpretedFunc();
		Expression body = valid_access_closure.getBodyExpr();
		Expression[] vars = valid_access_closure.getVars();

		assert (vars.length == 1);
		Expression bodyPrime = encoding.or(encoding.within(ptrExpr, sizeExpr,
		    vars[0]), body);

		PredicateClosure valid_access_closure_prime = suspend(func, bodyPrime,
		    vars[0]);
		state.putSafetyPredicateClosure(propName, valid_access_closure_prime);
	}

	private void updateHeapFunValidAccess(SingleLambdaStateExpression state,
	    Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS.name();
		PredicateClosure valid_access_closure = state.getSafetyPredicateClosure(
		    propName);

		Expression func = valid_access_closure.getUninterpretedFunc();
		Expression body = valid_access_closure.getBodyExpr();
		Expression[] vars = valid_access_closure.getVars();

		assert (vars.length == 1);
		Expression bodyPrime = encoding.or(encoding.and(ptrExpr.neq(formatter
		    .getNullAddress()), sizeExpr.neq(formatter.getSizeZero()), encoding
		        .within(ptrExpr, sizeExpr, vars[0])), body);

		PredicateClosure valid_access_closure_prime = suspend(func, bodyPrime,
		    vars[0]);
		state.putSafetyPredicateClosure(propName, valid_access_closure_prime);
	}

	private void updateStackFunValidAccessRange(SingleLambdaStateExpression state,
	    Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure valid_access_range_closure = state
		    .getSafetyPredicateClosure(propName);

		Expression func = valid_access_range_closure.getUninterpretedFunc();
		Expression body = valid_access_range_closure.getBodyExpr();
		Expression[] vars = valid_access_range_closure.getVars();

		assert (vars.length == 2);
		Expression bodyPrime = encoding.or(encoding.within(ptrExpr, sizeExpr,
		    vars[0], vars[1]), body);

		PredicateClosure valid_access_range_closure_prime = suspend(func, bodyPrime,
		    vars);
		state.putSafetyPredicateClosure(propName, valid_access_range_closure_prime);
	}

	private void updateHeapFunValidAccessRange(SingleLambdaStateExpression state,
	    Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure valid_access_range_closure = state
		    .getSafetyPredicateClosure(propName);

		Expression func = valid_access_range_closure.getUninterpretedFunc();
		Expression body = valid_access_range_closure.getBodyExpr();
		Expression[] vars = valid_access_range_closure.getVars();

		assert (vars.length == 2);
		Expression bodyPrime = encoding.or(encoding.and(ptrExpr.neq(formatter
		    .getNullAddress()), sizeExpr.neq(formatter.getSizeZero()), encoding
		        .within(ptrExpr, sizeExpr, vars[0], vars[1])), body);

		PredicateClosure valid_access_range_closure_prime = suspend(func, bodyPrime,
		    vars);
		state.putSafetyPredicateClosure(propName, valid_access_range_closure_prime);
	}

	private void updateFunHeapOrdered(SingleLambdaStateExpression state,
	    Expression ptrExpr, Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.HEAP_ORDERED.name();
		PredicateClosure heap_order_closure = state.getSafetyPredicateClosure(
		    propName);

		Expression func = heap_order_closure.getUninterpretedFunc();
		Expression[] vars = heap_order_closure.getVars();

		Expression ptrBound = encoding.plus(ptrExpr, sizeExpr);
		assert (vars.length == 1);

		// size might be zero.
		Expression bodyPrime = encoding.implies(ptrExpr.neq(formatter
		    .getNullAddress()), encoding.lessThan(ptrBound, vars[0]));

		PredicateClosure heap_order_closure_prime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, heap_order_closure_prime);
	}

	private void updateFunStackOrdred(SingleLambdaStateExpression state,
	    Expression ptrExpr) {
		String propName = SafetyPredicate.Kind.STACK_ORDERED.name();
		PredicateClosure stack_order_closure = state.getSafetyPredicateClosure(
		    propName);

		Expression func = stack_order_closure.getUninterpretedFunc();
		Expression[] vars = stack_order_closure.getVars();

		assert (vars.length == 1);
		Expression bodyPrime = encoding.lessThan(vars[0], ptrExpr);

		PredicateClosure stack_order_closure_prime = suspend(func, bodyPrime, vars);
		state.putSafetyPredicateClosure(propName, stack_order_closure_prime);
	}

	private void updateHeapPreDisjoint(SingleLambdaStateExpression state,
	    Expression ptrExpr, Expression sizeExpr) {
		String stackOrdered = SafetyPredicate.Kind.STACK_ORDERED.name();
		String heapOrdered = SafetyPredicate.Kind.HEAP_ORDERED.name();
		String preDisjoint = SafetyPredicate.Kind.PRE_DISJOINT.name();

		PredicateClosure stack_order_closure = state.getSafetyPredicateClosure(
		    stackOrdered);
		PredicateClosure heap_order_closure = state.getSafetyPredicateClosure(
		    heapOrdered);
		BooleanExpression pre_disjoint = state.getSafetyPredicate(preDisjoint);

		Expression ptrBound = encoding.plus(ptrExpr, sizeExpr);

		BooleanExpression pre_disjoint_prime = encoding.and(pre_disjoint, encoding
		    .implies(ptrExpr.neq(formatter.getNullAddress()), encoding.and(encoding
		        .notOverflow(ptrExpr, sizeExpr), stack_order_closure.eval(ptrBound),
		        heap_order_closure.eval(ptrExpr)))).asBooleanExpression();

		state.putSafetyPredicate(preDisjoint, pre_disjoint_prime);

		Expression stack_order_func = stack_order_closure.getUninterpretedFunc();
		Expression heap_order_func = heap_order_closure.getUninterpretedFunc();
		state.registerPredicate(stack_order_func, ptrBound);
		state.registerPredicate(heap_order_func, ptrExpr);
	}

	private void updateStackPreDisjoint(SingleLambdaStateExpression state,
	    Expression ptrExpr, Expression sizeExpr) {
		String stackOrdered = SafetyPredicate.Kind.STACK_ORDERED.name();
		String heapOrdered = SafetyPredicate.Kind.HEAP_ORDERED.name();
		String preDisjoint = SafetyPredicate.Kind.PRE_DISJOINT.name();

		PredicateClosure stack_order_closure = state.getSafetyPredicateClosure(
		    stackOrdered);
		PredicateClosure heap_order_closure = state.getSafetyPredicateClosure(
		    heapOrdered);
		BooleanExpression pre_disjoint = state.getSafetyPredicate(preDisjoint);

		Expression ptrBound = encoding.plus(ptrExpr, sizeExpr);

		BooleanExpression pre_disjoint_prime = encoding.and(pre_disjoint, ptrExpr
		    .neq(formatter.getNullAddress()), encoding.greaterThan(ptrBound,
		        ptrExpr), stack_order_closure.eval(ptrBound), heap_order_closure
		            .eval(ptrExpr)).asBooleanExpression();

		state.putSafetyPredicate(preDisjoint, pre_disjoint_prime);

		Expression stack_order_func = stack_order_closure.getUninterpretedFunc();
		Expression heap_order_func = heap_order_closure.getUninterpretedFunc();
		state.registerPredicate(stack_order_func, ptrBound);
		state.registerPredicate(heap_order_func, ptrExpr);
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
		PredicateClosure valid_access_closure = state.getSafetyPredicateClosure(
		    propName);

		Expression func = valid_access_closure.getUninterpretedFunc();
		Expression body = valid_access_closure.getBodyExpr();
		Expression[] vars = valid_access_closure.getVars();

		assert (vars.length == 1);
		Expression bodyPrime = encoding.and(body, encoding.not(encoding.within(
		    ptrExpr, sizeExpr, vars[0])));

		PredicateClosure valid_access_closure_prime = suspend(func, bodyPrime,
		    vars[0]);
		state.putSafetyPredicateClosure(propName, valid_access_closure_prime);
	}

	private void updateHeapFunValidAccessRangeFree(
	    SingleLambdaStateExpression state, Expression ptrExpr,
	    Expression sizeExpr) {
		String propName = SafetyPredicate.Kind.VALID_ACCESS_RANGE.name();
		PredicateClosure valid_access_range_closure = state
		    .getSafetyPredicateClosure(propName);

		Expression func = valid_access_range_closure.getUninterpretedFunc();
		Expression body = valid_access_range_closure.getBodyExpr();
		Expression[] vars = valid_access_range_closure.getVars();

		assert (vars.length == 2);
		Expression bodyPrime = encoding.and(body, encoding.not(encoding.within(
		    ptrExpr, sizeExpr, vars[0], vars[1])));

		PredicateClosure valid_access_range_closure_prime = suspend(func, bodyPrime,
		    vars);
		state.putSafetyPredicateClosure(propName, valid_access_range_closure_prime);
	}
}
