package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.util.EqualsUtil;
import edu.nyu.cascade.util.HashCodeUtil;

public class DefaultArrayEncoding implements ArrayEncoding<ArrayExpression> {
	private final ExpressionManager exprManager;

	public DefaultArrayEncoding(ExpressionManager exprManager) {
		this.exprManager = exprManager;
	}

	@Override
	public Instance<ArrayExpression> getInstance(TypeEncoding<?> indexEncoding,
			TypeEncoding<?> elementEncoding) {
		return new DefaultArrayInstance(exprManager, indexEncoding,
				elementEncoding);
	}

	@Override
	public boolean isEncodingFor(Expression x) {
		return x.isArray();
	}

	@Override
	public ArrayExpression ofExpression(Expression expr) {
		Preconditions.checkArgument(expr.isArray());
		return expr.asArray();
	}

	@Override
	public ExpressionManager getExpressionManager() {
		return exprManager;
	}

	@Override
	public Expression index(ArrayExpression array, Expression i) {
		return array.index(i);
	}

	@Override
	public ArrayExpression update(ArrayExpression array, Expression index,
			Expression elem) {
		return array.update(index, elem);
	}
}

class DefaultArrayInstance implements ArrayEncoding.Instance<ArrayExpression> {
	private final ExpressionManager exprManager;
	private final TypeEncoding<?> indexEncoding, elementEncoding;

	public DefaultArrayInstance(ExpressionManager exprManager,
			TypeEncoding<?> indexEncoding, TypeEncoding<?> elementEncoding) {
		this.exprManager = exprManager;
		this.indexEncoding = indexEncoding;
		this.elementEncoding = elementEncoding;
	}

	@Override
	public BooleanExpression eq(ArrayExpression lhs, ArrayExpression rhs) {
		return lhs.eq(rhs);
	}

	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof DefaultArrayInstance)) {
			return false;
		}
		DefaultArrayInstance instance = (DefaultArrayInstance) obj;
		return EqualsUtil.areEqual(exprManager, instance.exprManager)
				&& EqualsUtil.areEqual(indexEncoding, instance.indexEncoding)
				&& EqualsUtil.areEqual(elementEncoding, instance.elementEncoding);
	}

	@Override
	public TypeEncoding<?> getElementEncoding() {
		return elementEncoding;
	}

	public ExpressionManager getExpressionManager() {
		return exprManager;
	}

	@Override
	public TypeEncoding<?> getIndexEncoding() {
		return indexEncoding;
	}

	@Override
	public ArrayType getType() {
		return exprManager.arrayType(getIndexEncoding().getType(),
				getElementEncoding().getType());
	}

	@Override
	public int hashCode() {
		int hash = HashCodeUtil.SEED;
		hash = HashCodeUtil.hash(hash, exprManager);
		hash = HashCodeUtil.hash(hash, indexEncoding);
		hash = HashCodeUtil.hash(hash, elementEncoding);
		return hash;
	}

	@Override
	public Expression index(ArrayExpression array, Expression index) {
		return array.index(index);
	}

	@Override
	public boolean isEncodingFor(Expression x) {
		if (!x.isArray()) {
			return false;
		}
		ArrayExpression ax = x.asArray();
		return ax.getIndexType().equals(indexEncoding.getType())
				&& ax.getElementType().equals(elementEncoding.getType());
	}

	@Override
	public ArrayExpression ofExpression(Expression x) {
		Preconditions.checkArgument(x.isArray());
		return x.asArray();
	}

	@Override
	public ArrayExpression symbolicConstant(String name, boolean fresh) {
		return exprManager
				.arrayType(getIndexEncoding().getType(), getElementEncoding().getType())
				.variable(name, fresh);
	}

	@Override
	public ArrayExpression toArrayExpression(ArrayExpression array) {
		return array;
	}

	@Override
	public VariableExpression toVariable(ArrayExpression x) {
		Preconditions.checkArgument(x.isVariable());
		return x.asVariable();
	}

	@Override
	public ArrayExpression update(ArrayExpression array, Expression index,
			Expression val) {
		return array.update(index, val);
	}

	@Override
	public ArrayExpression variable(String name, boolean fresh) {
		return exprManager
				.arrayType(getIndexEncoding().getType(), getElementEncoding().getType())
				.variable(name, fresh);
	}

	@Override
	public ArrayExpression boundVar(String name, boolean fresh) {
		return exprManager
				.arrayType(getIndexEncoding().getType(), getElementEncoding().getType())
				.boundVar(name, fresh);
	}

	@Override
	public ArrayExpression boundExpression(String name, int index,
			boolean fresh) {
		return exprManager
				.arrayType(getIndexEncoding().getType(), getElementEncoding().getType())
				.boundExpression(name, index, fresh);
	}

	@Override
	public ArrayExpression variable(String name, IRType iType, boolean fresh) {
		return variable(name, fresh);
	}

	@Override
	public ArrayExpression boundVar(String name, IRType iType, boolean fresh) {
		return boundVar(name, fresh);
	}

	@Override
	public ArrayExpression boundExpression(String name, int index, IRType iType,
			boolean fresh) {
		return boundExpression(name, index, fresh);
	}
}
