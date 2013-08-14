package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public interface IntegerEncoding<T extends Expression> extends TypeEncoding<T> {
  /**
   * Returns a boolean expression representing the bitwise AND of the two
   * integer arguments.
   */
  T bitwiseAnd(T a, T b);

  /** Returns an integer expression representing the constant <code>c</code>. */
  T constant(int c);
  /**
   * Returns an integer expression representing the integer <code>expr</code>
   * minus one.
   */
  T decr(T expr);
  
  BooleanExpression distinct(Iterable<? extends T> exprs);

  /**
   * Returns a boolean expression comparing integers <code>lhs</code> and
   * <code>rhs</code> for equality.
   */
  BooleanExpression eq(T lhs, T rhs);

  /**
   * Returns a boolean expression comparing integers <code>lhs</code> and
   * <code>rhs</code>.
   */
  BooleanExpression greaterThan(T lhs, T rhs);
  
  /**
   * Returns a boolean expression comparing signed integers <code>lhs</code> 
   * and <code>rhs</code>.
   */
  BooleanExpression signedGreaterThan(T lhs, T rhs);

//  Class<T> getExpressionType();
  
  BooleanExpression greaterThanOrEqual(T lhs, T rhs);
  
  BooleanExpression signedGreaterThanOrEqual(T lhs, T rhs);
  
  T ifThenElse(BooleanExpression b, T thenExpr, T elseExpr);
  
  /**
   * Returns an integer expression representing the integer <code>expr</code>
   * plus one.
   */
  T incr(T expr);

  /**
   * Returns a boolean expression comparing integers <code>lhs</code> and
   * <code>rhs</code>.
   */
  BooleanExpression lessThan(T lhs, T rhs);
  
  /**
   * Returns a boolean expression comparing signed integers <code>lhs</code> and
   * <code>rhs</code>.
   */
  BooleanExpression signedLessThan(T lhs, T rhs);

  /**
   * Returns a boolean expression comparing integers <code>lhs</code> and
   * <code>rhs</code>.
   */
  BooleanExpression lessThanOrEqual(T lhs, T rhs);

  /**
   * Returns a boolean expression comparing signed integers <code>lhs</code> and
   * <code>rhs</code>.
   */
  BooleanExpression signedLessThanOrEqual(T lhs, T rhs);
  
  /**
   * Returns an integer expression representing subtraction of the two integer
   * arguments.
   */
  T minus(T lhs, T rhs);

  T negate(T arg);

  /**
   * Returns a boolean expression comparing integers <code>lhs</code> and
   * <code>rhs</code> for disequality.
   */
  BooleanExpression neq(T lhs, T rhs) ;
  T ofBoolean(BooleanExpression b);

  /**
   * Returns an integer expression representing one.
   */
  T one() ;
  
  T plus(Iterable<? extends T> args) ;

  T plus(T... args) ;

  /**
   * Returns an integer expression representing the sum of the two integer arguments.
   */
  T plus(T lhs, T rhs) ;
  
  /**
   * Returns an integer expression representing the product of the two integer arguments.
   */
  T times(T lhs, T rhs) ;
  
  /**
   * Returns an integer expression representing the quotient of the two integer arguments.
   */
  T divide(T lhs, T rhs);
  
  /**
   * Returns an integer expression representing the remainder of the two integer arguments.
   */
  T mod(T lhs, T rhs);

  BooleanExpression toBoolean(T expr);
  VariableExpression toVariable(T expr);
  
  T unknown();
  T unknown(Type type);
  /**
   * Returns an integer expression representing zero.
   */
  T zero() ;
}
