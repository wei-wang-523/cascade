package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;

public interface BooleanEncoding<T extends Expression> extends TypeEncoding<T> {
  T and(T lhs, T rhs);
  T and(Iterable<? extends T> conjuncts);
  /**
   * Returns the <code>ExpressionManager</code> object used in the underlying
   * expression encoding.
   */
  ExpressionManager getExpressionManager();
  T forall(Iterable<? extends VariableExpression> ids, T expr);
  T exists(Iterable<? extends VariableExpression> ids, T expr);
  T ff();
  T iff(T lhs, T rhs);
  T implies(T lhs, T rhs);
  T not(T arg);
  T ofBooleanExpression(BooleanExpression b);
  BooleanExpression toBoolean(T b);
  T or(T lhs, T rhs);
  T or(Iterable<? extends T> conjuncts);
  T tt();
  T xor(T lhs, T rhs);
  T unknown();
}
