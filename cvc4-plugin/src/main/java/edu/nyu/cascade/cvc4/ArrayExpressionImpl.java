package edu.nyu.cascade.cvc4;

import static edu.nyu.cascade.prover.Expression.Kind.ARRAY_UPDATE;
import static edu.nyu.cascade.prover.Expression.Kind.ARRAY_INDEX;
import static edu.nyu.cascade.prover.Expression.Kind.ARRAY_STORE_ALL;

import com.google.common.base.Preconditions;

import edu.nyu.acsys.CVC4.ArrayStoreAll;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

final class ArrayExpressionImpl extends ExpressionImpl
		implements ArrayExpression {

	static ArrayExpressionImpl mkStoreAll(ExpressionManagerImpl exprManager,
			Expression expr, Type arrayType) {
		Preconditions.checkArgument(
				expr.getType().equals(arrayType.asArrayType().getElementType()));
		return new ArrayExpressionImpl(exprManager, ARRAY_STORE_ALL,
				new ArrayStoreAllConstructionStrategy() {
					@Override
					public Expr apply(ExprManager em, edu.nyu.acsys.CVC4.ArrayType type,
							Expr expr) {
						return em.mkConst(new ArrayStoreAll(type, expr));
					}
				}, arrayType, expr);
	}

	static ArrayExpressionImpl mkUpdate(ExpressionManagerImpl exprManager,
			Expression array, Expression index, Expression value) {
		Preconditions.checkArgument(array.isArray());
		Preconditions
				.checkArgument(array.asArray().getIndexType().equals(index.getType()));
		Preconditions.checkArgument(
				array.asArray().getElementType().equals(value.getType()));
		return new ArrayExpressionImpl(exprManager, ARRAY_UPDATE,
				new TernaryConstructionStrategy() {
					@Override
					public Expr apply(ExprManager em, Expr arg1, Expr arg2, Expr arg3) {
						return em.mkExpr(edu.nyu.acsys.CVC4.Kind.STORE, arg1, arg2, arg3);
					}
				}, array, index, value);
	}

	static ExpressionImpl mkArrayIndex(ExpressionManagerImpl exprManager,
			Expression array, Expression index) {
		Preconditions.checkArgument(array.isArray());
		ExpressionImpl result = new ExpressionImpl(exprManager, ARRAY_INDEX,
				new BinaryConstructionStrategy() {
					@Override
					public Expr apply(ExprManager em, Expr left, Expr right) {
						return em.mkExpr(edu.nyu.acsys.CVC4.Kind.SELECT, left, right);
					}
				}, array, index);
		result.setType(array.asArray().getElementType());
		return result;
	}

	private final Type indexType;
	private final Type elementType;

	private ArrayExpressionImpl(ExpressionImpl expr) {
		super(expr);
		indexType = super.getType().asArrayType().getIndexType();
		elementType = super.getType().asArrayType().getElementType();
	}

	private ArrayExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
			TernaryConstructionStrategy strategy, Expression array, Expression index,
			Expression element) {
		super(exprManager, kind, strategy, array, index, element);
		indexType = index.getType();
		elementType = element.getType();
	}

	private ArrayExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
			ArrayStoreAllConstructionStrategy strategy, Type arrayType,
			Expression expr) {
		super(exprManager, kind, strategy, arrayType, expr);
		indexType = arrayType.asArrayType().getIndexType();
		elementType = arrayType.asArrayType().getElementType();
	}

	private ArrayExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
			Expr expr, ArrayType type, Iterable<? extends ExpressionImpl> children) {
		super(exprManager, kind, expr, type);
		indexType = type.getIndexType();
		elementType = type.getElementType();
	}

	protected static ArrayExpressionImpl create(ExpressionManagerImpl exprManager,
			Kind kind, Expr expr, ArrayType type,
			Iterable<? extends ExpressionImpl> children) {
		return new ArrayExpressionImpl(exprManager, kind, expr, type, children);
	}

	@Override
	public ArrayType getType() {
		return getExpressionManager().arrayType(indexType, elementType);
	}

	@Override
	public Type getIndexType() {
		return indexType;
	}

	@Override
	public Type getElementType() {
		return elementType;
	}

	@Override
	public ExpressionImpl index(Expression i) {
		return mkArrayIndex(getExpressionManager(), this, i);
	}

	@Override
	public ArrayExpressionImpl update(Expression i, Expression val) {
		return mkUpdate(getExpressionManager(), this, i, val);
	}

	static ArrayExpressionImpl valueOf(ExpressionImpl e) {
		Preconditions.checkArgument(e.isArray());
		if (e instanceof ArrayExpressionImpl) {
			return (ArrayExpressionImpl) e;
		} else {
			return new ArrayExpressionImpl(e);
		}
	}
}
