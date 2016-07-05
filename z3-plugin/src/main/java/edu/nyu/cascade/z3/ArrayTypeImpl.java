package edu.nyu.cascade.z3;

import com.google.common.base.Preconditions;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

final class ArrayTypeImpl extends TypeImpl implements ArrayType {
	private final Type indexType;
	private final Type elementType;

	static ArrayTypeImpl create(ExpressionManagerImpl exprManager, Type index,
			Type elem) {
		return new ArrayTypeImpl(exprManager, index, elem);
	}

	@Override
	ArrayExpressionImpl createExpression(Expr res, Expression oldExpr,
			Iterable<? extends ExpressionImpl> children) {
		return ArrayExpressionImpl.create(getExpressionManager(), oldExpr.getKind(),
				res, oldExpr.getType(), children);
	}

	static ArrayTypeImpl valueOf(ExpressionManagerImpl exprManager, Type type) {
		Preconditions.checkArgument(type.isArrayType());
		if (type instanceof ArrayTypeImpl) {
			return (ArrayTypeImpl) type;
		} else {
			ArrayType arrayType = type.asArrayType();
			return create(exprManager, arrayType.getIndexType(), arrayType
					.getElementType());
		}
	}

	private ArrayTypeImpl(ExpressionManagerImpl exprManager, Type index,
			Type elem) {
		super(exprManager);
		this.indexType = index;
		this.elementType = elem;
		try {
			Sort indexZ3Type = exprManager.toZ3Type(indexType);
			Sort elementZ3Type = exprManager.toZ3Type(elementType);
			setZ3Type(exprManager.getTheoremProver().getZ3Context().mkArraySort(
					indexZ3Type, elementZ3Type));
		} catch (Exception e) {
			throw new TheoremProverException(e);
		}
	}

	@Override
	public DomainType getDomainType() {
		return DomainType.ARRAY;
	}

	@Override
	public ArrayVariableImpl variable(String name, boolean fresh) {
		return ArrayVariableImpl.create(getExpressionManager(), name, this, fresh);
	}

	@Override
	public ArrayBoundExpressionImpl boundVar(String name, boolean fresh) {
		return ArrayBoundExpressionImpl.create(getExpressionManager(), name, this,
				fresh);
	}

	@Override
	public ArrayBoundExpressionImpl boundExpression(String name, int index,
			boolean fresh) {
		return ArrayBoundExpressionImpl.create(getExpressionManager(), name, index,
				this, fresh);
	}

	@Override
	public Type getElementType() {
		return elementType;
	}

	@Override
	public Type getIndexType() {
		return indexType;
	}

	@Override
	public String toString() {
		return "ARRAY " + getIndexType() + " OF " + getElementType();
	}

	@Override
	public String getName() {
		return toString();
	}

	@Override
	public ExpressionImpl importExpression(Expression expression) {
		switch (expression.getKind()) {
		/*
		 * case ARRAY_INDEX: assert( expression.getArity() == 2); return
		 * index((IExpression) expression.getChild(0), (IExpression)
		 * expression.getChild(1));
		 */

		case ARRAY_UPDATE:
			assert (expression.getArity() == 3);
			return ArrayExpressionImpl.mkUpdate(getExpressionManager(),
					(Expression) expression.getChild(0), (Expression) expression.getChild(
							1), (Expression) expression.getChild(2));

		default:
			return super.importExpression(expression);
		}
	}

	@Override
	public Expression index(Expression array, Expression index) {
		Preconditions.checkArgument(array.isArray());
		Preconditions.checkArgument(index.getType().equals(array.asArray()
				.getIndexType()));
		return ArrayExpressionImpl.mkArrayIndex(getExpressionManager(), array,
				index);
	}

	@Override
	public ArrayExpression update(Expression array, Expression index,
			Expression value) {
		Preconditions.checkArgument(array.isArray());
		Preconditions.checkArgument(index.getType().equals(array.asArray()
				.getIndexType()));
		Preconditions.checkArgument(value.getType().equals(array.asArray()
				.getElementType()));
		return ArrayExpressionImpl.mkUpdate(getExpressionManager(), array, index,
				value);
	}

	@Override
	public ArrayExpression storeAll(Expression expr, ArrayType type) {
		return ArrayExpressionImpl.mkStoreAll(getExpressionManager(), expr, type);
	}
}
