package edu.nyu.cascade.cvc4;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.Type;

final class TupleVariableImpl extends VariableExpressionImpl implements
    TupleExpression {

	static TupleVariableImpl create(ExpressionManagerImpl exprManager,
	    String name, TupleTypeImpl type, boolean fresh) {
		return new TupleVariableImpl(exprManager, name, type, fresh);
	}

	private TupleVariableImpl(ExpressionManagerImpl exprManager, String name,
	    TupleTypeImpl type, boolean fresh) {
		super(exprManager, name, type, fresh);
	}

	private TupleVariableImpl(ExpressionManagerImpl em, String name, Type type,
	    boolean fresh) {
		super(em, name, type, fresh);
		Preconditions.checkArgument(type.isTuple());
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
