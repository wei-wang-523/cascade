package edu.nyu.cascade.z3;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.Type;

final class ArrayBoundExpressionImpl extends BoundExpressionImpl implements
		ArrayExpression {

	static ArrayBoundExpressionImpl create(ExpressionManagerImpl em, String name,
			ArrayTypeImpl type, boolean fresh) {
		return new ArrayBoundExpressionImpl(em, name, type, fresh);
	}

	static ArrayBoundExpressionImpl create(ExpressionManagerImpl em, String name,
			int index, ArrayTypeImpl type, boolean fresh) {
		return new ArrayBoundExpressionImpl(em, name, index, type, fresh);
	}

	private ArrayBoundExpressionImpl(ExpressionManagerImpl em, String name,
			ArrayTypeImpl type, boolean fresh) {
		super(em, name, type, fresh);
	}

	private ArrayBoundExpressionImpl(ExpressionManagerImpl em, String name,
			int index, ArrayTypeImpl type, boolean fresh) {
		super(em, name, index, type, fresh);
	}

	@Override
	public ArrayTypeImpl getType() {
		return (ArrayTypeImpl) super.getType();
	}

	@Override
	public Type getElementType() {
		return getType().getElementType();
	}

	@Override
	public Type getIndexType() {
		return getType().getIndexType();
	}

	@Override
	public ExpressionImpl index(Expression i) {
		return ArrayExpressionImpl.mkArrayIndex(getExpressionManager(), this, i);
	}

	@Override
	public ArrayExpressionImpl update(Expression i, Expression val) {
		return ArrayExpressionImpl.mkUpdate(getExpressionManager(), this, i, val);
	}
}
