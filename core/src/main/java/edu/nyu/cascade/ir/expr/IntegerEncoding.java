package edu.nyu.cascade.ir.expr;

import java.math.BigInteger;

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
  
  /**
   * Returns a boolean expression representing the bitwise OR of the two
   * integer arguments.
   */
  T bitwiseOr(T a, T b);
  
  /** 
   * Returns a boolean expression representing the bitwise XOR of the two
   * integer arguments.
   */
  T bitwiseXor(T a, T b);
  
  /** 
   * Returns a boolean expression representing the bitwise Negate of the
   * integer argument.
   */
  T bitwiseNegate(T a);

  /** Returns an integer expression representing the constant <code>c</code>. */
  T constant(int c);
  
  T constant(long c);
  
  T constant(BigInteger c);
  
  /** Returns an integer expression representing the character constant <code>c</code>. */
  T characterConstant(int c);
  
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
   * @return a boolean expression comparing signed integers <code>lhs</code> and
   * <code>rhs</code>.
   */
  BooleanExpression signedLessThanOrEqual(T lhs, T rhs);
  
  /**
   * @return an integer expression representing subtraction of the two integer
   * arguments.
   */
  T minus(T lhs, T rhs);

  /**
   * @return an expression representing negation of <code>arg</code>
   */
  T negate(T arg);

  /**
   * @return a boolean expression comparing integers <code>lhs</code> and
   * <code>rhs</code> for inequality.
   */
  BooleanExpression neq(T lhs, T rhs) ;
  
  T ofBoolean(BooleanExpression b);

  /**
   * Cast expression <code>i</code> to integer expression with given <code>
   * size</code>
   */
  T ofInteger(T i, int size);
  
  /**
   * Cast expression <code>i</code> to integer expression with given <code>
   * size</code>
   */
  T ofInteger(T i, int size, boolean isSigned);
  
  /**
   * Returns an integer expression representing one.
   */
  T one() ;

  /**
   * @return an integer expression representing <code>\sigma(args)</code>.
   */
  T plus(T first, Iterable<? extends T> args) ;

  /**
   * @return an integer expression representing <code>\sigma(args)</code>.
   */
  T plus(T first, T... rest) ;

  /**
   * @return an integer expression representing <code>lhs + rhs</code>.
   */
  T plus(T lhs, T rhs) ;
  
  /**
   * @return an integer expression representing <code>lhs * rhs</code>
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

  /**
   * @return cast <code>expr</code> to boolean expression
   */
  BooleanExpression toBoolean(T expr);
  
  /**
   * @return cast <code>expr</code> to variable expression
   */
  VariableExpression toVariable(T expr);
  
  /**
   * @return an unknown expression
   */
  T unknown();
  
  /**
   * @return an unknown expression with given <code>type</code>
   */
  T unknown(long size);
  
  /**
   * Returns an integer expression representing zero.
   */
  T zero() ;
  
  /**
   * Return an expression representing <code>-expr</code>
   */
  T uminus(T expr);
  
  /**
   * Return an expression representing <code>+expr</code>
   */
  T uplus(T expr);
  
  /**
   * @return an expression representing <code>lhs << rhs</code>
   */
  T lshift(T lhs, T rhs);
  
  /**
   * @return an expression representing logic <code>lhs >> rhs</code>
   */
  T rshift(T lhs, T rhs);
  
  /**
   * @return an expression representing arithmetic <code>lhs >> rhs</code>
   */
  T signedRshift(T lhs, T rhs);
  
  /**
   * @return an expression representing <code>lhs % rhs</code>
   */
  T rem(T lhs, T rhs);
  
  /**
   * @return an expression representing signed integers <code>lhs % rhs</code>
   */
  T signedRem(T lhs, T rhs);
  
  /**
   * @return an expression representing signed integers <code>lhs / rhs</code>
   */
  T signedDivide(T lhs, T rhs);
  
  T variable(String name, Type type, boolean fresh);
}
