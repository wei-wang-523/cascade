package edu.nyu.cascade.z3;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TupleExpression;

final class TupleBoundExpressionImpl extends BoundExpressionImpl implements
    TupleExpression {

	static TupleBoundExpressionImpl create(ExpressionManagerImpl exprManager,
	    String name, TupleTypeImpl type, boolean fresh) {
		return new TupleBoundExpressionImpl(exprManager, name, type, fresh);
	}

	private TupleBoundExpressionImpl(ExpressionManagerImpl exprManager,
	    String name, TupleTypeImpl type, boolean fresh) {
		super(exprManager, name, type, fresh);
	}

	static TupleBoundExpressionImpl create(ExpressionManagerImpl exprManager,
	    String name, int index, TupleTypeImpl type, boolean fresh) {
		return new TupleBoundExpressionImpl(exprManager, name, index, type, fresh);
	}

	private TupleBoundExpressionImpl(ExpressionManagerImpl exprManager,
	    String name, int index, TupleTypeImpl type, boolean fresh) {
		super(exprManager, name, index, type, fresh);
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
