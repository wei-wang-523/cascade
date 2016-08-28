package edu.nyu.cascade.cvc4;

import java.util.Collections;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;

import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

final class BitVectorVariableImpl extends VariableExpressionImpl
		implements BitVectorExpression {

	BitVectorVariableImpl(ExpressionManagerImpl em, String name,
			BitVectorTypeImpl type, boolean fresh) {
		super(em, name, type, fresh);
	}

	@Override
	public BitVectorTypeImpl getType() {
		return (BitVectorTypeImpl) super.getType();
	}

	@Override
	public BitVectorExpressionImpl and(Expression a) {
		return BitVectorExpressionImpl.mkAnd(getExpressionManager(), this, a);

	}

	@Override
	public BitVectorExpressionImpl concat(Expression a) {
		return BitVectorExpressionImpl.mkConcat(getExpressionManager(), this, a);

	}

	@Override
	public BitVectorExpressionImpl extract(int i, int j) {
		return BitVectorExpressionImpl.mkExtract(getExpressionManager(), this, i,
				j);

	}

	@Override
	public int getSize() {
		return getType().getSize();
	}

	@Override
	public BitVectorExpressionImpl minus(Expression a) {
		return BitVectorExpressionImpl.mkMinus(getExpressionManager(), this, a);

	}

	@Override
	public BitVectorExpressionImpl nand(Expression a) {
		return BitVectorExpressionImpl.mkNand(getExpressionManager(), this, a);

	}

	@Override
	public BitVectorExpressionImpl nor(Expression a) {
		return BitVectorExpressionImpl.mkNor(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl not() {
		return BitVectorExpressionImpl.mkNot(getExpressionManager(), this);
	}

	@Override
	public BitVectorExpressionImpl neg() {
		return BitVectorExpressionImpl.mkNegate(getExpressionManager(), this);
	}

	@Override
	public BitVectorExpressionImpl or(Expression a) {
		return BitVectorExpressionImpl.mkOr(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl plus(Expression a) {
		return BitVectorExpressionImpl.mkPlus(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl plus(Expression... args) {
		return BitVectorExpressionImpl.mkPlus(getExpressionManager(), this, args);
	}

	@Override
	public BitVectorExpressionImpl plus(Iterable<? extends Expression> args) {
		return BitVectorExpressionImpl.mkPlus(getExpressionManager(),
				Iterables.concat(Collections.singletonList(this), args));
	}

	@Override
	public BitVectorExpressionImpl times(Expression a) {
		return BitVectorExpressionImpl.mkMult(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpression times(Expression... args) {
		return BitVectorExpressionImpl.mkMult(getExpressionManager(), this, args);
	}

	@Override
	public BitVectorExpression times(Iterable<? extends Expression> args) {
		return BitVectorExpressionImpl.mkMult(getExpressionManager(),
				Iterables.concat(Collections.singletonList(this), args));
	}

	@Override
	public BitVectorExpressionImpl divides(Expression a) {
		return BitVectorExpressionImpl.mkDivide(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl rems(Expression a) {
		return BitVectorExpressionImpl.mkRem(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl xnor(Expression a) {
		return BitVectorExpressionImpl.mkXnor(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl xor(Expression a) {
		return BitVectorExpressionImpl.mkXor(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl lshift(Expression a) {
		return BitVectorExpressionImpl.mkLShift(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl rshift(Expression a) {
		return BitVectorExpressionImpl.mkRShift(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpressionImpl signedRshift(Expression a) {
		return BitVectorExpressionImpl.mkSRShift(getExpressionManager(), this, a);
	}

	@Override
	public BooleanExpression greaterThan(Expression e) {
		Preconditions.checkArgument(e.isBitVector());
		return getType().geq(this, e);
	}

	@Override
	public BooleanExpression greaterThanOrEqual(Expression e) {
		Preconditions.checkArgument(e.isBitVector());
		return getType().geq(this, e);
	}

	@Override
	public BooleanExpression lessThan(Expression e) {
		Preconditions.checkArgument(e.isBitVector());
		return getType().geq(this, e);
	}

	@Override
	public BooleanExpression lessThanOrEqual(Expression e) {
		Preconditions.checkArgument(e.isBitVector());
		return getType().geq(this, e);
	}

	@Override
	public BitVectorExpression signedDivides(Expression a) {
		return BitVectorExpressionImpl.mkSDivide(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpression signedRems(Expression a) {
		return BitVectorExpressionImpl.mkSRem(getExpressionManager(), this, a);
	}

	@Override
	public BitVectorExpression zeroExtend(int size) {
		return BitVectorExpressionImpl.mkZeroExtend(getExpressionManager(), size,
				this);
	}

	@Override
	public BitVectorExpression signExtend(int size) {
		return BitVectorExpressionImpl.mkSignExtend(getExpressionManager(), size,
				this);
	}

	@Override
	public BitVectorExpression uminus() {
		return BitVectorExpressionImpl.mkUminus(getExpressionManager(), this);
	}
}
