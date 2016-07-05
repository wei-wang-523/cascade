package edu.nyu.cascade.z3;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.RationalExpression;
import edu.nyu.cascade.prover.type.Type;

final class RationalBoundExpressionImpl extends BoundExpressionImpl implements
		RationalExpression {

	static RationalBoundExpressionImpl create(ExpressionManagerImpl em,
			String name, Type type, boolean fresh) {
		Preconditions.checkArgument(type.isRational());
		return new RationalBoundExpressionImpl(em, name, type, fresh);
	}

	private RationalBoundExpressionImpl(ExpressionManagerImpl em, String name,
			Type type, boolean fresh) {
		super(em, name, type, fresh);
	}

	static RationalBoundExpressionImpl create(ExpressionManagerImpl em,
			String name, int index, Type type, boolean fresh) {
		Preconditions.checkArgument(type.isRational());
		return new RationalBoundExpressionImpl(em, name, index, type, fresh);
	}

	private RationalBoundExpressionImpl(ExpressionManagerImpl em, String name,
			int index, Type type, boolean fresh) {
		super(em, name, index, type, fresh);
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
