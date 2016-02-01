package edu.nyu.cascade.ir.memory.safety;

import java.util.Collection;

import edu.nyu.cascade.ir.state.SingleLambdaStateExpression;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.VariableExpression;

public interface IRMemSafetyEncoding {

	Expression validMalloc(Expression ptr, Expression size);
	
	BooleanExpression validFree(ArrayExpression sizeArr, Expression ptr);

	PredicateClosure suspend(Expression func, Expression expr, Expression... vars);

	void initMemSafetyPredicates(SingleLambdaStateExpression state);

	void updateStackMemSafetyPredicates(SingleLambdaStateExpression state,
			VariableExpression ptrExpr, VariableExpression sizeExpr);

	void updateHeapMemSafetyPredicates(SingleLambdaStateExpression state,
			VariableExpression ptrExpr, VariableExpression sizeExpr);

	/** Propagate the memory safety predicates of <code>fromState</code>
	 * to <code>toState</code>
	 * @param fromState
	 * @param toState
	 */
	void propagateSafetyPredicates(SingleLambdaStateExpression fromState, SingleLambdaStateExpression toState);

	/**
	 * Refresh the safety properties related to <code>state</code> with
	 * <code>fromLabels</code> to <code>toLabels</code>
	 * @param state
	 * @param fromLabels
	 * @param toLabels
	 */
	void refreshDuplicateLabels(SingleLambdaStateExpression state,
      Collection<VariableExpression> fromLabels,
      Collection<VariableExpression> toLabels);
	
	Collection<String> getExprPropNames();

	Collection<String> getClosurePropNames();

	/**
	 * Get the current (updated) predicate corresponding to <code>predicate</code>, 
	 * from <code>state</code>, and apply it to <code>args</code> 
	 * 
	 * @param state
	 * @param predicate
	 * @param args
	 * @return
	 */
	Expression applyUpdatedPredicate(SingleLambdaStateExpression state, 
			FunctionExpression predicate,
      Collection<Expression> args);

	Expression getInitBoolValue(Expression key);
	
	PredicateClosure getValidAccess(SingleLambdaStateExpression state);
	
	PredicateClosure getValidAccessRange(SingleLambdaStateExpression state);
	
	BooleanExpression getPreDisjoint(SingleLambdaStateExpression state);
}
