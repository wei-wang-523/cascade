package edu.nyu.cascade.z3;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TupleExpression;

final class TupleVariableImpl extends VariableExpressionImpl
		implements TupleExpression {

	static TupleVariableImpl create(ExpressionManagerImpl exprManager,
			String name, TupleTypeImpl type, boolean fresh) {
		return new TupleVariableImpl(exprManager, name, type, fresh);
	}

	private TupleVariableImpl(ExpressionManagerImpl exprManager, String name,
			TupleTypeImpl type, boolean fresh) {
		super(exprManager, name, type, fresh);
	}

	@Override
	public TupleTypeImpl getType() {
		return (TupleTypeImpl) super.getType();
	}

	@Override
	public int size() {
		return getType().size();
	}

	@Override
	public Expression index(int i) {
		return TupleExpressionImpl.mkTupleIndex(getExpressionManager(), this, i);
	}

	@Override
	public TupleExpression update(int index, Expression val) {
		return TupleExpressionImpl.mkUpdate(getExpressionManager(), this, index,
				val);
	}
}
