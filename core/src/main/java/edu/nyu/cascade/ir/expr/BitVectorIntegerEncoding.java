package edu.nyu.cascade.ir.expr;

import java.util.Arrays;

import com.google.inject.internal.Preconditions;

import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.BitVectorType;

public class BitVectorIntegerEncoding extends
    AbstractTypeEncoding<BitVectorExpression> implements
    IntegerEncoding<BitVectorExpression> {
  private static final String UNKNOWN_VARIABLE_NAME = "bv_encoding_unknown";
  
  public static BitVectorIntegerEncoding create(ExpressionManager exprManager, int size) {
    BitVectorType type = exprManager.bitVectorType(size);
    return new BitVectorIntegerEncoding(exprManager, type);
  }
  
  private BitVectorIntegerEncoding(ExpressionManager exprManager, BitVectorType type) {
    super(exprManager, type);
  }
  
  @Override
  public BitVectorExpression bitwiseAnd(BitVectorExpression a,
      BitVectorExpression b) {
    return a.and(b);
  }

  @Override
  public BitVectorExpression constant(int c) {
    return getExpressionManager().bitVectorConstant(c, getType().getSize());
  }

  @Override
  public BitVectorExpression decr(BitVectorExpression expr) {
    return expr.minus(one());
  }

  @Override
  public BooleanExpression distinct(
      Iterable<? extends BitVectorExpression> exprs) {
    return getExpressionManager().distinct(exprs);
  }

  @Override
  public BitVectorType getType() {
    return super.getType().asBitVectorType();
  }
  
  @Override
  public BooleanExpression greaterThan(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().greaterThan(lhs, rhs);
  }
  
  @Override
  public BooleanExpression signedGreaterThan(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().signedGreaterThan(lhs, rhs);
  }
  
  @Override
  public BooleanExpression greaterThanOrEqual(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().greaterThanOrEqual(lhs, rhs);
  }

  @Override
  public BooleanExpression signedGreaterThanOrEqual(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().signedGreaterThanOrEqual(lhs, rhs);
  }

  @Override
  public BitVectorExpression ifThenElse(BooleanExpression b,
      BitVectorExpression thenExpr, BitVectorExpression elseExpr) {
    return b.ifThenElse(thenExpr, elseExpr).asBitVector();
  }

  @Override
  public BitVectorExpression incr(BitVectorExpression expr) {
    return expr.plus(getType().getSize(),one());
  }

  @Override
  public BooleanExpression lessThan(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().lessThan(lhs, rhs);
  }
  
  @Override
  public BooleanExpression signedLessThan(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().signedLessThan(lhs, rhs);
  }

  @Override
  public BooleanExpression lessThanOrEqual(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().lessThanOrEqual(lhs, rhs);
  }
  
  @Override
  public BooleanExpression signedLessThanOrEqual(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().signedLessThanOrEqual(lhs, rhs);
  }

  @Override
  public BitVectorExpression minus(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().bitVectorMinus(lhs, rhs);
  }

  @Override
  public BitVectorExpression negate(BitVectorExpression arg) {
    return incr(arg.not());
  }

  @Override
  public BooleanExpression neq(BitVectorExpression lhs, BitVectorExpression rhs) {
    return lhs.neq(rhs);
  }

  @Override
  public BitVectorExpression ofBoolean(BooleanExpression b) {
    return b.ifThenElse(one(), zero()).asBitVector();
  }

  @Override
  public BitVectorExpression one() {
    return constant(1);
  }

  @Override
  public BitVectorExpression plus(Iterable<? extends BitVectorExpression> args) {
    return getExpressionManager().bitVectorPlus(getType().getSize(),args);
  }

  @Override
  public BitVectorExpression plus(BitVectorExpression... args) {
    return plus(Arrays.asList(args));
  }

  @Override
  public BitVectorExpression plus(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.plus(getType().getSize(), rhs);
  }

  @Override
  public BitVectorExpression times(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.times(getType().getSize(), rhs);
  }
  
  @Override
  public BitVectorExpression divide(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.divides(rhs);
  }
  
  @Override
  public BitVectorExpression mod(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.signedRems(rhs);
  }
  
  @Override
  public BooleanExpression toBoolean(BitVectorExpression expr) {
    return expr.neq(zero());
  }

  @Override
  public BitVectorExpression unknown() {
    return variable(UNKNOWN_VARIABLE_NAME, true);
  }

  @Override
  public BitVectorExpression zero() {
    return constant(0);
  }

  @Override
  public BitVectorExpression ofExpression(Expression x) {
    Preconditions.checkArgument(x.isBitVector());
    return x.asBitVector();
  }
  
  public BitVectorExpression lshift(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.lshift(rhs);
  }
  
  public BitVectorExpression rshift(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.rshift(rhs);
  }
  
  public BitVectorExpression signedDivide(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.signedDivides(rhs);
  }
  
  public BitVectorExpression rem(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.rems(rhs);
  }
  
  public BitVectorExpression signedRem(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.signedRems(rhs);
  }
}
