package edu.nyu.cascade.z3;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.RecordExpression;

final class RecordBoundExpressionImpl extends BoundExpressionImpl implements
		RecordExpression {

	static RecordBoundExpressionImpl create(ExpressionManagerImpl exprManager,
			String name, RecordTypeImpl type, boolean fresh) {
		return new RecordBoundExpressionImpl(exprManager, name, type, fresh);
	}

	private RecordBoundExpressionImpl(ExpressionManagerImpl exprManager,
			String name, RecordTypeImpl type, boolean fresh) {
		super(exprManager, name, type, fresh);
	}

	static RecordBoundExpressionImpl create(ExpressionManagerImpl exprManager,
			String name, int index, RecordTypeImpl type, boolean fresh) {
		return new RecordBoundExpressionImpl(exprManager, name, index, type, fresh);
	}

	private RecordBoundExpressionImpl(ExpressionManagerImpl exprManager,
			String name, int index, RecordTypeImpl type, boolean fresh) {
		super(exprManager, name, index, type, fresh);
	}

	@Override
	public RecordTypeImpl getType() {
		return (RecordTypeImpl) super.getType();
	}

	@Override
	public Expression select(String name) {
		return select(name);
	}

	@Override
	public RecordExpression update(String name, Expression val) {
		return update(name, val);
	}
}
