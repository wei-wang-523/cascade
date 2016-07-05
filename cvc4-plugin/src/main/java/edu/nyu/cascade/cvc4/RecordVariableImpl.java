package edu.nyu.cascade.cvc4;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.type.Type;

final class RecordVariableImpl extends VariableExpressionImpl implements
		RecordExpression {

	static RecordVariableImpl create(ExpressionManagerImpl exprManager,
			String name, RecordTypeImpl type, boolean fresh) {
		return new RecordVariableImpl(exprManager, name, type, fresh);
	}

	private RecordVariableImpl(ExpressionManagerImpl exprManager, String name,
			RecordTypeImpl type, boolean fresh) {
		super(exprManager, name, type, fresh);
	}

	private RecordVariableImpl(ExpressionManagerImpl em, String name, Type type,
			boolean fresh) {
		super(em, name, type, fresh);
		Preconditions.checkArgument(type.isRecord());
	}

	@Override
	public RecordTypeImpl getType() {
		return (RecordTypeImpl) super.getType();
	}

	@Override
	public Expression select(String name) {
		return RecordExpressionImpl.mkRecordIndex(getExpressionManager(), this,
				name);
	}

	@Override
	public RecordExpression update(String name, Expression val) {
		return RecordExpressionImpl.mkUpdate(getExpressionManager(), this, name,
				val);
	}
}
