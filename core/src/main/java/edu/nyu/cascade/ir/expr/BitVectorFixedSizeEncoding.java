package edu.nyu.cascade.ir.expr;

import java.math.BigInteger;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;

public class BitVectorFixedSizeEncoding extends
    AbstractTypeEncoding<BitVectorExpression> implements
    IntegerEncoding<BitVectorExpression> {
	
	private static final String UNKNOWN_VARIABLE_NAME = "bv_encoding_unknown";
	
	private final BitVectorIntegerEncoding intEncoding;
	
	public static BitVectorFixedSizeEncoding create(ExpressionManager exprManager,
			BitVectorIntegerEncoding intEncoding, int size) {
    BitVectorType type = exprManager.bitVectorType(size);
    return new BitVectorFixedSizeEncoding(exprManager, type, intEncoding);
  }
  
  private BitVectorFixedSizeEncoding(ExpressionManager exprManager, BitVectorType type, 
  		BitVectorIntegerEncoding _intEncoding) {
    super(exprManager, type);
    intEncoding = _intEncoding;
  }
  
  @Override
  public BitVectorType getType() {
  	return super.getType().asBitVectorType();
  }

	@Override
  public BitVectorExpression ofExpression(Expression x) {
	  return intEncoding.ofExpression(x);
  }

	@Override
  public BitVectorExpression bitwiseAnd(BitVectorExpression a,
      BitVectorExpression b) {
	  return intEncoding.bitwiseAnd(a, b);
  }

	@Override
  public BitVectorExpression constant(int c) {
	  return getExpressionManager().bitVectorConstant(c, getType().getSize());
  }

	@Override
  public BitVectorExpression constant(long c) {
		return getExpressionManager().bitVectorConstant(c, getType().getSize());
  }

	@Override
  public BitVectorExpression constant(BigInteger c) {
		return getExpressionManager().bitVectorConstant(c, getType().getSize());
  }

	@Override
  public BitVectorExpression decr(BitVectorExpression expr) {
		Preconditions.checkArgument(expr.getType().equals(getType()));
	  return minus(expr, one());
  }

	@Override
  public BooleanExpression distinct(
      Iterable<? extends BitVectorExpression> exprs) {
	  return intEncoding.distinct(exprs);
  }

	@Override
  public BooleanExpression greaterThan(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
	  return intEncoding.greaterThan(lhs, rhs);
  }

	@Override
  public BooleanExpression signedGreaterThan(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
	  return intEncoding.signedGreaterThan(lhs, rhs);
  }

	@Override
  public BooleanExpression greaterThanOrEqual(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
	  return intEncoding.greaterThanOrEqual(lhs, rhs);
  }

	@Override
  public BooleanExpression signedGreaterThanOrEqual(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
	  return intEncoding.signedGreaterThanOrEqual(lhs, rhs);
  }

	@Override
  public BitVectorExpression ifThenElse(BooleanExpression b,
      BitVectorExpression thenExpr, BitVectorExpression elseExpr) {
	  Preconditions.checkArgument(thenExpr.getType().equals(getType()));
	  Preconditions.checkArgument(elseExpr.getType().equals(getType()));
	  return intEncoding.ifThenElse(b, thenExpr, elseExpr);
  }

	@Override
  public BitVectorExpression incr(BitVectorExpression expr) {
	  Preconditions.checkArgument(expr.getType().equals(getType()));
	  return plus(expr, one());
  }

	@Override
  public BooleanExpression lessThan(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
	  return intEncoding.lessThan(lhs, rhs);
  }

	@Override
  public BooleanExpression signedLessThan(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
	  return intEncoding.signedLessThan(lhs, rhs);
  }

	@Override
  public BooleanExpression lessThanOrEqual(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
	  return intEncoding.lessThanOrEqual(lhs, rhs);
  }

	@Override
  public BooleanExpression signedLessThanOrEqual(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
	  return intEncoding.signedLessThanOrEqual(lhs, rhs);
  }

	@Override
  public BitVectorExpression minus(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
	  return intEncoding.minus(lhs, rhs);
  }

	@Override
  public BitVectorExpression negate(BitVectorExpression arg) {
    return incr(arg.not());
  }

	@Override
  public BooleanExpression neq(BitVectorExpression lhs, BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
		return intEncoding.neq(lhs, rhs);
  }

	@Override
  public BitVectorExpression ofBoolean(BooleanExpression b) {
		return b.ifThenElse(one(), zero()).asBitVector();
  }

	@Override
  public BitVectorExpression ofInteger(BitVectorExpression i, int size) {
		Preconditions.checkArgument(i.getType().equals(getType()));
		Preconditions.checkArgument(size == getType().getSize());
		return i;
  }

	@Override
  public BitVectorExpression one() {
	  return constant(1);
  }

	@Override
  public BitVectorExpression plus(Iterable<? extends BitVectorExpression> args) {
		Preconditions.checkArgument(Iterables.all(args, new Predicate<BitVectorExpression>(){
			@Override
			public boolean apply(BitVectorExpression arg) {
				return arg.getType().equals(getType());
			}
		}));
		return intEncoding.plus(args);
  }

	@Override
  public BitVectorExpression plus(BitVectorExpression... args) {
	  return plus(Lists.newArrayList(args));
  }

	@Override
  public BitVectorExpression plus(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().getSize() <= getType().getSize());
		Preconditions.checkArgument(rhs.getType().getSize() <= getType().getSize());
		if(lhs.getType().getSize() < getType().getSize())
			lhs = lhs.signExtend(getType().getSize());
		if(rhs.getType().getSize() < getType().getSize())
			rhs = rhs.signExtend(getType().getSize());
		return intEncoding.plus(lhs, rhs);
  }

	@Override
  public BitVectorExpression times(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
		return intEncoding.times(lhs, rhs);
  }

	@Override
  public BitVectorExpression divide(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
		return intEncoding.divide(lhs, rhs);
  }

	@Override
  public BitVectorExpression mod(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
		return intEncoding.mod(lhs, rhs);
  }

	@Override
  public BooleanExpression toBoolean(BitVectorExpression expr) {
		Preconditions.checkArgument(expr.getType().equals(getType()));
		return intEncoding.toBoolean(expr);
  }

	@Override
  public BitVectorExpression unknown() {
	  return variable(UNKNOWN_VARIABLE_NAME, true);
  }

	@Override
  public BitVectorExpression unknown(Type type) {
	  return intEncoding.unknown(type);
  }

	@Override
  public BitVectorExpression zero() {
		return constant(0);
  }

	@Override
  public BitVectorExpression uminus(BitVectorExpression expr) {
	  Preconditions.checkArgument(expr.getType().equals(getType()));
	  return intEncoding.uminus(expr);
  }

	@Override
  public BitVectorExpression lshift(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
		return intEncoding.lshift(lhs, rhs);
  }

	@Override
  public BitVectorExpression rshift(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
		return intEncoding.rshift(lhs, rhs);
  }

	@Override
  public BitVectorExpression rem(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
		return intEncoding.rem(lhs, rhs);
  }

	@Override
  public BitVectorExpression signedRem(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
		return intEncoding.signedRem(lhs, rhs);
  }

	@Override
  public BitVectorExpression signedDivide(BitVectorExpression lhs,
      BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
		return intEncoding.signedDivide(lhs, rhs);
  }
	
	@Override
	public BooleanExpression eq(BitVectorExpression lhs, BitVectorExpression rhs) {
		Preconditions.checkArgument(lhs.getType().equals(getType()));
		Preconditions.checkArgument(rhs.getType().equals(getType()));
		return intEncoding.eq(lhs, rhs);
	}
}
