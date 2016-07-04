package edu.nyu.cascade.cvc4;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TupleExpression;

final class TupleBoundVariableImpl extends BoundVariableExpressionImpl
    implements TupleExpression {

	static TupleBoundVariableImpl create(ExpressionManagerImpl exprManager,
	    String name, TupleTypeImpl type, boolean fresh) {
		return new TupleBoundVariableImpl(exprManager, name, type, fresh);
	}

	private TupleBoundVariableImpl(ExpressionManagerImpl exprManager, String name,
	    TupleTypeImpl type, boolean fresh) {
		super(exprManager, name, type, fresh);
	}

	@Override
	public TupleTypeImpl getType() {
		return (TupleTypeImpl) super.getType();
	}

	@Override
	public Expression index(int i) {
		return TupleExpressionImpl.mkTupleIndex(getExpressionManager(), this, i);
	}

	@Override
	public int size() {
		return getType().size();
	}

	@Override
	public TupleExpression update(int index, Expression val) {
		return TupleExpressionImpl.mkUpdate(getExpressionManager(), this, index,
		    val);
	}
}
