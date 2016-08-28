package edu.nyu.cascade.ir.expr;

import java.math.BigInteger;

import xtc.type.NumberT;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.type.IRIntegerType;
import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;

public class BitVectorIntegerEncoding
		extends AbstractTypeEncoding<BitVectorExpression>
		implements IntegerEncoding<BitVectorExpression> {
	private static final String UNKNOWN_VARIABLE_NAME = "bv_encoding_unknown";

	public static BitVectorIntegerEncoding create(ExpressionManager exprManager) {
		int wordSize = CType.getInstance().getWordSize();
		BitVectorType type = exprManager.bitVectorType(wordSize);
		return new BitVectorIntegerEncoding(exprManager, type);
	}

	private BitVectorIntegerEncoding(ExpressionManager exprManager,
			BitVectorType type) {
		super(exprManager, type);
	}

	@Override
	public BitVectorExpression bitwiseAnd(BitVectorExpression a,
			BitVectorExpression b) {
		return a.and(b);
	}

	@Override
	public BitVectorExpression bitwiseOr(BitVectorExpression a,
			BitVectorExpression b) {
		return a.or(b);
	}

	@Override
	public BitVectorExpression bitwiseXor(BitVectorExpression a,
			BitVectorExpression b) {
		return a.xor(b);
	}

	@Override
	public BitVectorExpression bitwiseNegate(BitVectorExpression a) {
		return a.not();
	}

	@Override
	public BitVectorExpression characterConstant(int c) {
		return getExpressionManager().bitVectorConstant(c,
				(int) getCTypeAnalyzer().getWidth(NumberT.CHAR));
	}

	@Override
	public BitVectorExpression constant(int c) {
		return getExpressionManager().bitVectorConstant(c,
				(int) getCTypeAnalyzer().getWidth(NumberT.INT));
	}

	@Override
	public BitVectorExpression constant(long c) {
		return getExpressionManager().bitVectorConstant(c,
				(int) getCTypeAnalyzer().getWidth(NumberT.LONG));
	}

	@Override
	public BitVectorExpression constant(BigInteger c, long size) {
		ExpressionManager exprManager = getExpressionManager();
		return exprManager.bitVectorConstant(c, (int) size);
	}

	@Override
	public BitVectorExpression decr(BitVectorExpression expr) {
		return minus(expr, one());
	}

	@Override
	public BitVectorExpression incr(BitVectorExpression expr) {
		return plus(expr, one());
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
	public BooleanExpression neq(BitVectorExpression lhs,
			BitVectorExpression rhs) {
		return lhs.neq(rhs);
	}

	@Override
	public BitVectorExpression ofBoolean(BooleanExpression b) {
		return b.ifThenElse(one(), zero()).asBitVector();
	}

	@Override
	public BitVectorExpression ofInteger(BitVectorExpression bv, int size) {
		return ofInteger(bv, size, true);
	}

	@Override
	public BitVectorExpression ofInteger(BitVectorExpression bv, int size,
			boolean isSigned) {
		int srcSize = bv.getSize();
		if (srcSize == size)
			return bv;
		if (srcSize > size)
			return bv.extract(size - 1, 0);

		return isSigned ? bv.signExtend(size) : bv.zeroExtend(size);
	}

	@Override
	public BitVectorExpression plus(BitVectorExpression first,
			Iterable<? extends BitVectorExpression> rest) {
		return first.plus(rest);
	}

	@Override
	public BitVectorExpression plus(BitVectorExpression first,
			BitVectorExpression... rest) {
		return first.plus(rest);
	}

	@Override
	public BitVectorExpression plus(BitVectorExpression lhs,
			BitVectorExpression rhs) {
		return lhs.plus(rhs);
	}

	@Override
	public BitVectorExpression times(BitVectorExpression lhs,
			BitVectorExpression rhs) {
		return lhs.times(rhs);
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
		int size = expr.getType().getSize();
		Expression zero = getExpressionManager().bitVectorZero(size);
		return expr.neq(zero);
	}

	@Override
	public BitVectorExpression unknown() {
		return getType().asBitVectorType().variable(UNKNOWN_VARIABLE_NAME, true);
	}

	@Override
	public BitVectorExpression unknown(long size) {
		BitVectorType bvType = getExpressionManager().bitVectorType((int) size);
		return bvType.variable(UNKNOWN_VARIABLE_NAME, true);
	}

	@Override
	public BitVectorExpression one() {
		return constant(1);
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

	@Override
	public boolean isEncodingFor(Expression x) {
		return x.getType().isBitVectorType();
	}

	@Override
	public BitVectorExpression lshift(BitVectorExpression lhs,
			BitVectorExpression rhs) {
		return lhs.lshift(rhs);
	}

	@Override
	public BitVectorExpression rshift(BitVectorExpression lhs,
			BitVectorExpression rhs) {
		return lhs.rshift(rhs);
	}

	@Override
	public BitVectorExpression signedRshift(BitVectorExpression lhs,
			BitVectorExpression rhs) {
		return lhs.signedRshift(rhs);
	}

	@Override
	public BitVectorExpression signedDivide(BitVectorExpression lhs,
			BitVectorExpression rhs) {
		return lhs.signedDivides(rhs);
	}

	@Override
	public BitVectorExpression rem(BitVectorExpression lhs,
			BitVectorExpression rhs) {
		return lhs.rems(rhs);
	}

	@Override
	public BitVectorExpression signedRem(BitVectorExpression lhs,
			BitVectorExpression rhs) {
		return lhs.signedRems(rhs);
	}

	@Override
	public BitVectorExpression uminus(BitVectorExpression expr) {
		return expr.uminus();
	}

	@Override
	public BitVectorExpression uplus(BitVectorExpression expr) {
		return expr;
	}

	@Override
	public BooleanExpression eq(BitVectorExpression lhs,
			BitVectorExpression rhs) {
		if (lhs.getSize() > rhs.getSize())
			rhs = rhs.signExtend(lhs.getSize());
		if (lhs.getSize() < rhs.getSize())
			lhs = lhs.signExtend(rhs.getSize());
		return lhs.eq((Expression) rhs);
	}

	@Override
	public BitVectorExpression variable(String name, Type type, boolean fresh) {
		Preconditions.checkArgument(type.isBitVectorType());
		return type.asBitVectorType().variable(name, fresh);
	}

	@Override
	public BitVectorExpression variable(String name, IRType iType,
			boolean fresh) {
		Preconditions.checkArgument(iType.getKind().equals(IRType.Kind.INTEGER));
		int size = (int) getCTypeAnalyzer()
				.getWidth(((IRIntegerType) iType).getSrcType());
		Type intType = getExpressionManager().bitVectorType(size);
		return variable(name, intType, fresh);
	}
}
