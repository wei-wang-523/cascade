package edu.nyu.cascade.cvc4;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.RationalExpression;
import edu.nyu.cascade.prover.type.Type;

final class RationalBoundVariableImpl extends BoundVariableExpressionImpl
    implements RationalExpression {

	static RationalBoundVariableImpl create(ExpressionManagerImpl em, String name,
	    Type type, boolean fresh) {
		Preconditions.checkArgument(type.isRational());
		return new RationalBoundVariableImpl(em, name, type, fresh);
	}

	/** Create a new variable of a rational sub-type (e.g., a range type). */
	private RationalBoundVariableImpl(ExpressionManagerImpl em, String name,
	    Type type, boolean fresh) {
		super(em, name, type, fresh);
	}

	@Override
	public RationalTypeImpl getType() {
		return getExpressionManager().rationalType();
	}

	@Override
	public RationalExpressionImpl divide(Expression e) {
		return getType().divide(this, e);
	}

	@Override
	public BooleanExpressionImpl gt(Expression e) {
		return getType().gt(this, e);
	}

	@Override
	public BooleanExpressionImpl geq(Expression e) {
		return getType().geq(this, e);
	}

	@Override
	public BooleanExpressionImpl lt(Expression e) {
		return getType().lt(this, e);
	}

	@Override
	public BooleanExpressionImpl leq(Expression e) {
		return getType().leq(this, e);
	}

	@Override
	public RationalExpressionImpl mult(Expression e) {
		return getType().mult(this, e);
	}

	@Override
	public RationalExpressionImpl pow(Expression exp) {
		return getType().pow(this, exp);
	}

	@Override
	public RationalExpressionImpl minus(Expression e) {
		return getType().subtract(this, e);
	}

	@Override
	public RationalExpressionImpl plus(Expression e) {
		return getType().add(this, e);
	}
}
