package edu.nyu.cascade.cvc4;

import com.google.common.base.Preconditions;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.Expression.Kind;
import edu.nyu.cascade.prover.type.RationalType;

class RationalTypeImpl extends TypeImpl implements RationalType {
	RationalTypeImpl(ExpressionManagerImpl expressionManager) {
		super(expressionManager);
		setCVC4Type(
				expressionManager.getTheoremProver().getCvc4ExprManager().realType());
	}

	protected RationalTypeImpl(ExpressionManagerImpl em,
			BinaryConstructionStrategy strategy, Expression lowerBound,
			Expression upperBound) {
		super(em, strategy, lowerBound, upperBound);
	}

	@Override
	public RationalExpressionImpl add(Expression first, Expression... rest) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException(
				"RationalType.add(IExpression,IExpression...);");
	}

	@Override
	public RationalExpressionImpl add(Expression a, Expression b) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException(
				"RationalType.add(IExpression,IExpression);");
	}

	@Override
	public RationalExpressionImpl add(Iterable<? extends Expression> addends) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("RationalType.add(Iterable);");
	}

	@Override
	public RationalExpressionImpl constant(int numerator, int denominator) {
		return RationalExpressionImpl.mkConstant(getExpressionManager(), numerator,
				denominator);
	}

	@Override
	public RationalExpressionImpl divide(Expression a, Expression b) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public BooleanExpressionImpl geq(Expression a, Expression b) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public BooleanExpressionImpl sgeq(Expression a, Expression b) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public DomainType getDomainType() {
		return DomainType.RATIONAL;
	}

	@Override
	public String getName() {
		return "REAL";
	}

	@Override
	public BooleanExpressionImpl gt(Expression a, Expression b) {
		return BooleanExpressionImpl.mkGt(getExpressionManager(), a, b);
	}

	@Override
	public BooleanExpressionImpl sgt(Expression a, Expression b) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public BooleanExpressionImpl leq(Expression a, Expression b) {
		return BooleanExpressionImpl.mkLeq(getExpressionManager(), a, b);
	}

	@Override
	public BooleanExpressionImpl sleq(Expression a, Expression b) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public BooleanExpressionImpl lt(Expression a, Expression b) {
		return BooleanExpressionImpl.mkLt(getExpressionManager(), a, b);
	}

	@Override
	public BooleanExpressionImpl slt(Expression a, Expression b) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public RationalExpressionImpl mult(Expression left, Expression right) {
		return RationalExpressionImpl.mkMult(getExpressionManager(), left, right);
	}

	/*
	 * @Override public RationalExpression mult( List<? extends IExpression>
	 * terms) { return RationalExpression.mkMult(getExpressionManager(),terms); }
	 */

	@Override
	public RationalExpressionImpl negate(Expression a) {
		return RationalExpressionImpl.mkUminus(getExpressionManager(), a);
	}

	@Override
	public RationalExpressionImpl one() {
		return RationalExpressionImpl.mkConstant(getExpressionManager(), 1, 1);
	}

	@Override
	public RationalExpressionImpl pow(Expression base, Expression exp) {
		return RationalExpressionImpl.mkPow(getExpressionManager(), base, exp);
	}

	@Override
	public RationalExpressionImpl subtract(Expression a, Expression b) {
		return RationalExpressionImpl.mkMinus(getExpressionManager(), a, b);
	}

	@Override
	public RationalVariableImpl variable(String name, boolean fresh) {
		return RationalVariableImpl.create(getExpressionManager(), name, this,
				fresh);
	}

	@Override
	public RationalBoundVariableImpl boundVar(String name, boolean fresh) {
		return RationalBoundVariableImpl.create(getExpressionManager(), name, this,
				fresh);
	}

	@Override
	public RationalBoundVariableImpl boundExpression(String name, int index,
			boolean fresh) {
		return boundVar(name, fresh);
	}

	@Override
	public RationalExpressionImpl zero() {
		return RationalExpressionImpl.mkConstant(getExpressionManager(), 0, 1);
	}

	@Override
	public Expression mult(Iterable<? extends Expression> terms) {
		return RationalExpressionImpl.mkMult(getExpressionManager(), terms);
	}

	@Override
	RationalExpressionImpl createExpression(Expr res, Expression e, Kind kind,
			Iterable<ExpressionImpl> children) {
		Preconditions.checkArgument(e.isRational());
		return RationalExpressionImpl.create(getExpressionManager(), kind, res,
				e.getType().asRational(), children);
	}
}
