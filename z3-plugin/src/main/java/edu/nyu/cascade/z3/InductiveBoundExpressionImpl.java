package edu.nyu.cascade.z3;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.InductiveExpression;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.Selector;

final class InductiveBoundExpressionImpl extends BoundExpressionImpl
		implements InductiveExpression {

	static InductiveBoundExpressionImpl create(ExpressionManagerImpl em,
			String name, InductiveTypeImpl type, boolean fresh) {
		return new InductiveBoundExpressionImpl(em, name, type, fresh);
	}

	private InductiveBoundExpressionImpl(ExpressionManagerImpl em, String name,
			InductiveTypeImpl type, boolean fresh) {
		super(em, name, type, fresh);
	}

	static InductiveBoundExpressionImpl create(ExpressionManagerImpl em,
			String name, int index, InductiveTypeImpl type, boolean fresh) {
		return new InductiveBoundExpressionImpl(em, name, index, type, fresh);
	}

	private InductiveBoundExpressionImpl(ExpressionManagerImpl em, String name,
			int index, InductiveTypeImpl type, boolean fresh) {
		super(em, name, index, type, fresh);
	}

	@Override
	public InductiveTypeImpl getType() {
		return (InductiveTypeImpl) super.getType();
	}

	@Override
	public Expression select(Selector selector) {
		return selector.apply(this);
	}

	@Override
	public BooleanExpression test(Constructor constructor) {
		return getType().test(constructor, this);
	}
}
