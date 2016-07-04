package edu.nyu.cascade.ir.expr;

import java.math.BigInteger;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;

/**
 * Used for linear pointer encoding
 * 
 * @author Wei
 *
 */
public class BitVectorFixedSizeEncoding extends
    AbstractTypeEncoding<BitVectorExpression> implements
    IntegerEncoding<BitVectorExpression> {

	private final BitVectorIntegerEncoding intEncoding;

	public static BitVectorFixedSizeEncoding create(ExpressionManager exprManager,
	    BitVectorIntegerEncoding intEncoding, long size) {
		BitVectorType type = exprManager.bitVectorType((int) size);
		return new BitVectorFixedSizeEncoding(exprManager, type, intEncoding);
	}

	private BitVectorFixedSizeEncoding(ExpressionManager exprManager,
	    BitVectorType type, BitVectorIntegerEncoding _intEncoding) {
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
	public BitVectorExpression bitwiseAnd(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.bitwiseAnd(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BitVectorExpression bitwiseOr(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.bitwiseOr(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BitVectorExpression bitwiseXor(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.bitwiseXor(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BitVectorExpression bitwiseNegate(BitVectorExpression a) {
		return intEncoding.bitwiseNegate(typeConversion(a));
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
	public BitVectorExpression characterConstant(int c) {
		return getExpressionManager().bitVectorConstant(c, getType().getSize());
	}

	@Override
	public BitVectorExpression constant(BigInteger c, long size) {
		return getExpressionManager().bitVectorConstant(c, (int) size);
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
		return intEncoding.greaterThan(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BooleanExpression signedGreaterThan(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.signedGreaterThan(typeConversion(lhs), typeConversion(
		    rhs));
	}

	@Override
	public BooleanExpression greaterThanOrEqual(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.greaterThanOrEqual(typeConversion(lhs), typeConversion(
		    rhs));
	}

	@Override
	public BooleanExpression signedGreaterThanOrEqual(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.signedGreaterThanOrEqual(typeConversion(lhs),
		    typeConversion(rhs));
	}

	@Override
	public BitVectorExpression ifThenElse(BooleanExpression b,
	    BitVectorExpression thenExpr, BitVectorExpression elseExpr) {
		Preconditions.checkArgument(thenExpr.getType().equals(getType()));
		Preconditions.checkArgument(elseExpr.getType().equals(getType()));
		return intEncoding.ifThenElse(b, typeConversion(thenExpr), typeConversion(
		    elseExpr));
	}

	@Override
	public BitVectorExpression incr(BitVectorExpression expr) {
		Preconditions.checkArgument(expr.getType().equals(getType()));
		return plus(expr, one());
	}

	@Override
	public BooleanExpression lessThan(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.lessThan(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BooleanExpression signedLessThan(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.signedLessThan(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BooleanExpression lessThanOrEqual(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.lessThanOrEqual(typeConversion(lhs), typeConversion(
		    rhs));
	}

	@Override
	public BooleanExpression signedLessThanOrEqual(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.signedLessThanOrEqual(typeConversion(lhs),
		    typeConversion(rhs));
	}

	@Override
	public BitVectorExpression minus(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.minus(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BitVectorExpression negate(BitVectorExpression arg) {
		return incr(arg.not());
	}

	@Override
	public BooleanExpression neq(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.neq(typeConversion(lhs), typeConversion(rhs));
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
	public BitVectorExpression ofInteger(BitVectorExpression i, int size,
	    boolean isSigned) {
		Preconditions.checkArgument(i.getType().equals(getType()));
		Preconditions.checkArgument(size == getType().getSize());
		return i;
	}

	@Override
	public BitVectorExpression one() {
		return constant(1);
	}

	@Override
	public BitVectorExpression plus(BitVectorExpression first,
	    Iterable<? extends BitVectorExpression> rest) {
		Iterable<BitVectorExpression> argsPrime = Iterables.transform(rest,
		    new Function<BitVectorExpression, BitVectorExpression>() {
			    @Override
			    public BitVectorExpression apply(BitVectorExpression input) {
				    return typeConversion(input);
			    }
		    });
		return intEncoding.plus(typeConversion(first), argsPrime);
	}

	@Override
	public BitVectorExpression plus(BitVectorExpression first,
	    BitVectorExpression... rest) {
		return plus(first, rest);
	}

	@Override
	public BitVectorExpression plus(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.plus(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BitVectorExpression times(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.times(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BitVectorExpression divide(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.divide(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BitVectorExpression mod(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.mod(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BooleanExpression toBoolean(BitVectorExpression expr) {
		Preconditions.checkArgument(expr.getType().equals(getType()));
		return intEncoding.toBoolean(expr);
	}

	@Override
	public BitVectorExpression unknown() {
		return intEncoding.unknown();
	}

	@Override
	public BitVectorExpression unknown(long size) {
		return intEncoding.unknown(size);
	}

	@Override
	public BitVectorExpression zero() {
		return constant(0);
	}

	@Override
	public BitVectorExpression uminus(BitVectorExpression expr) {
		return intEncoding.uminus(typeConversion(expr));
	}

	@Override
	public BitVectorExpression uplus(BitVectorExpression expr) {
		return intEncoding.uplus(typeConversion(expr));
	}

	@Override
	public BitVectorExpression lshift(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.lshift(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BitVectorExpression rshift(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.rshift(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BitVectorExpression signedRshift(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.signedRshift(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BitVectorExpression rem(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.rem(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BitVectorExpression signedRem(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.signedRem(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BitVectorExpression signedDivide(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.signedDivide(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BooleanExpression eq(BitVectorExpression lhs,
	    BitVectorExpression rhs) {
		return intEncoding.eq(typeConversion(lhs), typeConversion(rhs));
	}

	@Override
	public BitVectorExpression variable(String name, Type type, boolean fresh) {
		Preconditions.checkArgument(type.isBitVectorType());
		return type.asBitVectorType().variable(name, fresh);
	}

	private BitVectorExpression typeConversion(BitVectorExpression bvExpr) {
		Preconditions.checkArgument(bvExpr.getSize() <= getType().getSize());

		int exprSize = bvExpr.getSize(), size = getType().getSize();

		if (exprSize == size)
			return bvExpr;
		return bvExpr.zeroExtend(size);
	}
}
