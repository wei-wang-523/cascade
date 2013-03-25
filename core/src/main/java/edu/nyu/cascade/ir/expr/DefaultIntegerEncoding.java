package edu.nyu.cascade.ir.expr;

import java.util.Arrays;

import com.google.inject.internal.Preconditions;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.IntegerExpression;

public class DefaultIntegerEncoding extends
    AbstractTypeEncoding<IntegerExpression> implements
    IntegerEncoding<IntegerExpression> {
  private static final String UNKNOWN_VARIABLE_NAME = "int_encoding_unknown";

  public DefaultIntegerEncoding(ExpressionManager exprManager) {
    super(exprManager, exprManager.integerType());
  }

  @Override
  public IntegerExpression bitwiseAnd(IntegerExpression a, IntegerExpression b) {
    return unknown();
  }

  @Override
  public IntegerExpression constant(int c) {
    return getExpressionManager().constant(c);
  }

  @Override
  public IntegerExpression decr(IntegerExpression expr) {
    return expr.minus(one());
  }

  @Override
  public BooleanExpression distinct(Iterable<? extends IntegerExpression> exprs) {
    return getExpressionManager().distinct(exprs);
  }

  @Override
  public BooleanExpression greaterThan(IntegerExpression lhs,
      IntegerExpression rhs) {
    return lhs.greaterThan(rhs);
  }
  

  @Override
  public BooleanExpression signedGreaterThan(IntegerExpression lhs,
      IntegerExpression rhs) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanExpression greaterThanOrEqual(IntegerExpression lhs,
      IntegerExpression rhs) {
    return lhs.greaterThanOrEqual(rhs);
  }

  @Override
  public BooleanExpression signedGreaterThanOrEqual(IntegerExpression lhs,
      IntegerExpression rhs) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public IntegerExpression ifThenElse(BooleanExpression b,
      IntegerExpression thenExpr, IntegerExpression elseExpr) {
    return b.ifThenElse(thenExpr, elseExpr).asIntegerExpression();
  }

  @Override
  public IntegerExpression incr(IntegerExpression expr) {
    return expr.plus(one());
  }

  @Override
  public BooleanExpression lessThan(IntegerExpression lhs, IntegerExpression rhs) {
    return lhs.lessThan(rhs);
  }
  
  @Override
  public BooleanExpression signedLessThan(IntegerExpression lhs, IntegerExpression rhs) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanExpression lessThanOrEqual(IntegerExpression lhs,
      IntegerExpression rhs) {
    return lhs.lessThanOrEqual(rhs);
  }
  
  @Override
  public BooleanExpression signedLessThanOrEqual(IntegerExpression lhs, IntegerExpression rhs) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public IntegerExpression minus(IntegerExpression lhs, IntegerExpression rhs) {
    return lhs.minus(rhs);
  }
  
  @Override
  public IntegerExpression times(IntegerExpression lhs, IntegerExpression rhs) {
    return lhs.times(rhs);
  }
  
  @Override
  public IntegerExpression divide(IntegerExpression lhs, IntegerExpression rhs) {
    return lhs.divides(rhs);
  }
  
  @Override
  public IntegerExpression mod(IntegerExpression lhs, IntegerExpression rhs) {
    return lhs.mods(rhs);
  }

  @Override
  public IntegerExpression negate(IntegerExpression arg) {
    return arg.negate();
  }

  @Override
  public BooleanExpression neq(IntegerExpression lhs, IntegerExpression rhs) {
    return lhs.neq(rhs);
  }

  @Override
  public IntegerExpression ofBoolean(BooleanExpression b) {
    return ifThenElse(b, one(), zero());
  }

  @Override
  public IntegerExpression ofExpression(Expression x) {
    Preconditions.checkArgument(x.isInteger());
    return x.asIntegerExpression();
  }

  @Override
  public IntegerExpression one() {
    return getExpressionManager().one();
  }

  @Override
  public IntegerExpression plus(IntegerExpression... args) {
    return plus(Arrays.asList(args));
  }

  @Override
  public IntegerExpression plus(IntegerExpression lhs, IntegerExpression rhs) {
    return lhs.plus(rhs);
  }

  @Override
  public IntegerExpression plus(Iterable<? extends IntegerExpression> args) {
    return getExpressionManager().plus(args).asIntegerExpression();
  }

  @Override
  public BooleanExpression toBoolean(IntegerExpression expr) {
    return expr.neq(zero());
  }

  @Override
  public IntegerExpression unknown() {
    return variable(UNKNOWN_VARIABLE_NAME, true);
  }

  @Override
  public IntegerExpression zero() {
    return getExpressionManager().zero();
  }

}