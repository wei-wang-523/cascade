package edu.nyu.cascade.z3;

import java.util.Collections;

import com.google.common.collect.Iterables;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.type.Type;

final class IntegerVariableImpl extends VariableExpressionImpl implements
		IntegerExpression {

	/** Create a new variable of an integer subtype (e.g., a range type). */
	IntegerVariableImpl(ExpressionManagerImpl em, String name, Type type,
			boolean fresh) {
		super(em, name, type, fresh);
	}

	@Override
	public IntegerTypeImpl getType() {
		return (IntegerTypeImpl) super.getType();
	}

	@Override
	public BooleanExpressionImpl greaterThan(Expression e) {
		return getType().gt(this, e);
	}

	@Override
	public BooleanExpressionImpl greaterThanOrEqual(Expression e) {
		return getType().geq(this, e);
	}

	@Override
	public BooleanExpression lessThan(Expression e) {
		return getType().lt(this, e);
	}

	@Override
	public BooleanExpression lessThanOrEqual(Expression e) {
		return getType().leq(this, e);
	}

	@Override
	public IntegerExpression minus(Expression e) {
		return getType().subtract(this, e);
	}

	@Override
	public IntegerExpression negate() {
		return getType().negate(this);
	}

	@Override
	public IntegerExpression plus(Expression e) {
		return getType().add(this, e);
	}

	@Override
	public IntegerExpression plus(IntegerExpression... rest) {
		return getType().add(this, rest);
	}

	@Override
	public IntegerExpression plus(Iterable<? extends IntegerExpression> rest) {
		return getType().add(Iterables.concat(Collections.singletonList(this),
				rest));
	}

	@Override
	public IntegerExpression pow(Expression e) {
		return getType().pow(this, e);
	}

	@Override
	public IntegerExpression times(Expression e) {
		return getType().mult(this, e);
	}

	@Override
	public IntegerExpression divides(Expression e) {
		return getType().divide(this, e);
	}

	@Override
	public IntegerExpression mods(Expression e) {
		return getType().mod(this, e);
	}
}
