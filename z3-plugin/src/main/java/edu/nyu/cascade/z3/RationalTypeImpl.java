package edu.nyu.cascade.z3;

import com.microsoft.z3.Expr;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.RationalType;

final class RationalTypeImpl extends TypeImpl implements RationalType {

	RationalTypeImpl(ExpressionManagerImpl expressionManager) {
		super(expressionManager);
		try {
			setZ3Type(expressionManager.getTheoremProver().getZ3Context()
			    .getRealSort());
		} catch (Z3Exception e) {
			throw new TheoremProverException(e);
		}
	}

	RationalTypeImpl(ExpressionManagerImpl em,
	    BinaryConstructionStrategy strategy, Expression lowerBound,
	    Expression upperBound) {
		super(em, strategy, lowerBound, upperBound);
	}

	@Override
	public RationalExpressionImpl add(Expression first, Expression... rest) {
		throw new UnsupportedOperationException(
		    "RationalType.add(IExpression,IExpression...);");
	}

	@Override
	public RationalExpressionImpl add(Expression a, Expression b) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public RationalExpressionImpl add(Iterable<? extends Expression> addends) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
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
	public RationalExpressionImpl zero() {
		return RationalExpressionImpl.mkConstant(getExpressionManager(), 0, 1);
	}

	@Override
	public Expression mult(Iterable<? extends Expression> terms) {
		return RationalExpressionImpl.mkMult(getExpressionManager(), terms);
	}

	@Override
	public RationalBoundExpressionImpl boundVar(String name, boolean fresh) {
		return RationalBoundExpressionImpl.create(getExpressionManager(), name,
		    this, fresh);
	}

	@Override
	public RationalBoundExpressionImpl boundExpression(String name, int index,
	    boolean fresh) {
		return RationalBoundExpressionImpl.create(getExpressionManager(), name,
		    index, this, fresh);
	}

	@Override
	protected InductiveExpressionImpl createExpression(Expr res,
	    Expression oldExpr, Iterable<? extends ExpressionImpl> children) {
		return InductiveExpressionImpl.create(getExpressionManager(), oldExpr
		    .getKind(), res, oldExpr.getType(), children);
	}
}
