package edu.nyu.cascade.cvc4;

import edu.nyu.cascade.prover.UninterpretedExpression;

final class UninterpretedBoundVariableImpl extends BoundVariableExpressionImpl
		implements UninterpretedExpression {

	static UninterpretedBoundVariableImpl create(
			ExpressionManagerImpl exprManager, String name,
			UninterpretedTypeImpl type, boolean fresh) {
		return new UninterpretedBoundVariableImpl(exprManager, name, type, fresh);
	}

	private UninterpretedBoundVariableImpl(ExpressionManagerImpl exprManager,
			String name, UninterpretedTypeImpl type, boolean fresh) {
		super(exprManager, name, type, fresh);
	}

	@Override
	public UninterpretedTypeImpl getType() {
		return (UninterpretedTypeImpl) super.getType();
	}
}
