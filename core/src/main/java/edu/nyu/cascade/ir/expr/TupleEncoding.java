package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public interface TupleEncoding<T extends Expression> {
  /** An instance of the encoding, for given element types. */
  public interface Instance<T extends Expression> extends TypeEncoding<T> {
    TupleExpression toTupleExpression(T tuple);
    Expression index(T tuple, int index);
    T update(T tuple, int index, Expression elem);
    Iterable<TypeEncoding<?>> getElementsEncoding();
  }
  
  /**
   * Returns the <code>ExpressionManager</code> object used in the underlying
   * expression encoding.
   */
  ExpressionManager getExpressionManager();
  Instance<T> getInstance(Iterable<TypeEncoding<?>> elementsEncoding);
  Expression index(T tuple, int index);
  T update(T tuple, int index, Expression elem);
  boolean isEncodingFor(Expression x);
  T ofExpression(Expression expr);
  
  T decr(T expr);
  BooleanExpression greaterThan(T lhs, T rhs);
  BooleanExpression greaterThanOrEqual(T lhs, T rhs);
  BooleanExpression lessThan(T lhs, T rhs);
  BooleanExpression lessThanOrEqual(T lhs, T rhs);
  T ifThenElse(BooleanExpression b, T thenExpr,
      T elseExpr);
  T incr(T expr);
  T minus(T lhs, Expression rhs);
  T plus(T first, Iterable<? extends Expression> rest);
  T plus(T first, Expression... rest);
  T plus(T first, Expression rest);
  BooleanExpression castToBoolean(T expr);
  BooleanExpression neq(T lhs, T rhs);
  BooleanExpression eq(T lhs, T rhs);
}
