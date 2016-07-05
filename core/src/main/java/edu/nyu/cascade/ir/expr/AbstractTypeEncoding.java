package edu.nyu.cascade.ir.expr;

import java.util.List;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public abstract class AbstractTypeEncoding<E extends Expression> implements
		TypeEncoding<E> {
	private final ExpressionManager exprManager;
	private final Type type;

	protected AbstractTypeEncoding(ExpressionManager exprManager, Type type) {
		this.exprManager = exprManager;
		this.type = type;
	}

	protected AbstractTypeEncoding(ExpressionManager exprManager, Type type,
			List<TypeEncoding<?>> subEncodings) {
		this.exprManager = exprManager;
		this.type = type;
	}

	@Override
	public BooleanExpression eq(E lhs, E rhs) {
		return lhs.eq((Expression) rhs);
	}

	public ExpressionManager getExpressionManager() {
		return exprManager;
	}

	public CType getCTypeAnalyzer() {
		return CType.getInstance();
	}

	@Override
	public Type getType() {
		return type;
	}

	@Override
	public boolean isEncodingFor(Expression x) {
		return getType().equals(x.getType());
	}

	@SuppressWarnings("unchecked")
	@Override
	public E symbolicConstant(String name, boolean fresh) {
		return (E) exprManager.variable(name, type, fresh);
	}

	/*
	 * @Override public EncodingValue toEncodingValue(E x) { return new
	 * EncodingValueImpl(x, this); }
	 */
	/*
	 * @Override public Expression<T> toExpression(E x) { return x; }
	 */

	@Override
	public VariableExpression toVariable(E expr) {
		Preconditions.checkArgument(expr.isVariable());
		return expr.asVariable();
	}

	/**
	 * Use the default type as the type of the variable, only bit-vector integer
	 * encoding needs the <code>iType</code> to get the actual bit-vector type of
	 * the variable.
	 */
	@Override
	public E variable(String name, IRType iType, boolean fresh) {
		return variable(name, fresh);
	}

	/**
	 * Use the default type as the type of bound variable, only bit-vector integer
	 * encoding needs the <code>iType</code> to get the actual bit-vector type of
	 * the bound variable.
	 */
	@Override
	public E boundVar(String name, IRType iType, boolean fresh) {
		return boundVar(name, fresh);
	}

	/**
	 * Use the default type as the type of the bound Expression, only bit-vector
	 * integer encoding needs the <code>iType</code> to get the actual bit-vector
	 * type of the bound Expression.
	 */
	@Override
	public E boundExpression(String name, int index, IRType iType,
			boolean fresh) {
		return boundExpression(name, index, fresh);
	}

	@SuppressWarnings("unchecked")
	@Override
	public E variable(String name, boolean fresh) {
		return (E) exprManager.variable(name, type, fresh);
	}

	@SuppressWarnings("unchecked")
	@Override
	public E boundVar(String name, boolean fresh) {
		return (E) exprManager.boundVar(name, type, fresh);
	}

	/**
	 * Use the default type as the type of the bound Expression, only bit-vector
	 * integer encoding needs the <code>iType</code> to get the actual bit-vector
	 * type of the bound Expression.
	 */
	@SuppressWarnings("unchecked")
	@Override
	public E boundExpression(String name, int index, boolean fresh) {
		return (E) exprManager.boundExpression(name, index, type, fresh);
	}
}
