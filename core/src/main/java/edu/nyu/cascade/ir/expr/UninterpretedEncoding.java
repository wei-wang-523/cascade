package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.VariableExpression;

public interface UninterpretedEncoding<T extends Expression> extends
		TypeEncoding<T> {

	BooleanExpression distinct(Iterable<? extends T> exprs);

	/**
	 * Returns a boolean expression comparing integers <code>lhs</code> and
	 * <code>rhs</code> for equality.
	 */
	BooleanExpression eq(T lhs, T rhs);

	/**
	 * Returns a boolean expression comparing integers <code>lhs</code> and
	 * <code>rhs</code> for disequality.
	 */
	BooleanExpression neq(T lhs, T rhs);

	T ifThenElse(BooleanExpression b, T thenExpr, T elseExpr);

	VariableExpression toVariable(T expr);

	T unknown();
}
