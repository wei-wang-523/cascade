package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public interface PointerEncoding<T extends Expression> extends TypeEncoding<T> {
  /**
   * Returns the <code>ExpressionManager</code> object used in the underlying
   * expression encoding.
   */
  ExpressionManager getExpressionManager();
  boolean isEncodingFor(Expression x);
  T ofExpression(Expression expr);
  
  T ifThenElse(BooleanExpression b, T thenExpr,
      T elseExpr);
  T incr(T expr);
  T decr(T expr);
  T minus(T lhs, Expression rhs);
  T plus(T first, Iterable<? extends Expression> rest);
  T plus(T first, Expression... rest);
  T plus(T first, Expression rest);
  BooleanExpression toBoolean(T expr);
  BooleanExpression neq(T lhs, T rhs);
  BooleanExpression eq(T lhs, T rhs);
  BooleanExpression greaterThan(T lhs, T rhs);
  BooleanExpression greaterThanOrEqual(T lhs, T rhs);
  BooleanExpression lessThan(T lhs, T rhs);
  BooleanExpression lessThanOrEqual(T lhs, T rhs);
	T getNullPtr();
	T unknown();
	T freshPtr(String name, boolean fresh);
}
