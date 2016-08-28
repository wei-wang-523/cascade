package edu.nyu.cascade.cvc4;

import edu.nyu.cascade.prover.UninterpretedExpression;

final class UninterpretedVariableImpl extends VariableExpressionImpl
		implements UninterpretedExpression {

	static UninterpretedVariableImpl create(ExpressionManagerImpl exprManager,
			String name, UninterpretedTypeImpl type, boolean fresh) {
		return new UninterpretedVariableImpl(exprManager, name, type, fresh);
	}

	private UninterpretedVariableImpl(ExpressionManagerImpl exprManager,
			String name, UninterpretedTypeImpl type, boolean fresh) {
		super(exprManager, name, type, fresh);
	}

	@Override
	public UninterpretedTypeImpl getType() {
		return (UninterpretedTypeImpl) super.getType();
	}
}
