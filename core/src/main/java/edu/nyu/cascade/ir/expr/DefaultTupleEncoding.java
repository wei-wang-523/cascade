package edu.nyu.cascade.ir.expr;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.EqualsUtil;
import edu.nyu.cascade.util.HashCodeUtil;

public class DefaultTupleEncoding implements TupleEncoding<TupleExpression> {
	private final ExpressionManager exprManager;

	public DefaultTupleEncoding(ExpressionManager exprManager) {
		this.exprManager = exprManager;
	}

	@Override
	public ExpressionManager getExpressionManager() {
		return exprManager;
	}

	@Override
	public edu.nyu.cascade.ir.expr.TupleEncoding.Instance<TupleExpression> getInstance(
	    String name, Iterable<TypeEncoding<?>> elementEncodings) {
		return new DefaultTupleInstance(exprManager, name, elementEncodings);
	}

	@Override
	public edu.nyu.cascade.ir.expr.TupleEncoding.Instance<TupleExpression> getInstance(
	    String name, TypeEncoding<?>... elementEncodings) {
		return new DefaultTupleInstance(exprManager, name, elementEncodings);
	}

	@Override
	public Expression index(TupleExpression tuple, int index) {
		return tuple.index(index);
	}

	@Override
	public TupleExpression update(TupleExpression tuple, int index,
	    Expression elem) {
		return tuple.update(index, elem);
	}

	@Override
	public boolean isEncodingFor(Expression x) {
		return x.isTuple();
	}

	@Override
	public TupleExpression ofExpression(Expression expr) {
		Preconditions.checkArgument(expr.isTuple());
		return expr.asTuple();
	}

	class DefaultTupleInstance implements
	    TupleEncoding.Instance<TupleExpression> {
		private final ExpressionManager exprManager;
		private final Iterable<TypeEncoding<?>> elementEncodings;
		private final String name;

		public DefaultTupleInstance(ExpressionManager exprManager, String name,
		    Iterable<TypeEncoding<?>> elementEncodings) {
			Preconditions.checkArgument(Iterables.size(elementEncodings) >= 2);
			this.exprManager = exprManager;
			this.name = name;
			this.elementEncodings = elementEncodings;
		}

		public DefaultTupleInstance(ExpressionManager exprManager, String name,
		    TypeEncoding<?>... elementEncodings) {
			Preconditions.checkArgument(elementEncodings.length >= 2);
			this.exprManager = exprManager;
			this.name = name;
			this.elementEncodings = Lists.newArrayList(elementEncodings);
		}

		@Override
		public BooleanExpression eq(TupleExpression lhs, TupleExpression rhs) {
			return lhs.eq(rhs);
		}

		public boolean equals(Object obj) {
			if (this == obj) {
				return true;
			}
			if (!(obj instanceof DefaultTupleInstance)) {
				return false;
			}
			DefaultTupleInstance instance = (DefaultTupleInstance) obj;
			return EqualsUtil.areEqual(exprManager, instance.exprManager)
			    && EqualsUtil.areEqual(elementEncodings, instance.elementEncodings);
		}

		@Override
		public String getName() {
			return name;
		}

		@Override
		public Iterable<TypeEncoding<?>> getElementEncodings() {
			return elementEncodings;
		}

		public ExpressionManager getExpressionManager() {
			return exprManager;
		}

		@Override
		public TupleType getType() {
			return getExpressionManager().tupleType(name, Iterables.transform(
			    getElementEncodings(), new Function<TypeEncoding<?>, Type>() {
				    @Override
				    public Type apply(TypeEncoding<?> encoding) {
					    return encoding.getType();
				    }
			    }));
		}

		@Override
		public int hashCode() {
			int hash = HashCodeUtil.SEED;
			hash = HashCodeUtil.hash(hash, exprManager);
			for (TypeEncoding<?> encoding : elementEncodings) {
				hash = HashCodeUtil.hash(hash, encoding);
			}
			return hash;
		}

		@Override
		public Expression index(TupleExpression tuple, int index) {
			return tuple.index(index);
		}

		@Override
		public boolean isEncodingFor(Expression x) {
			if (!x.isTuple())
				return false;
			TupleExpression ax = x.asTuple();
			return ax.getType().equals(getType());
		}

		@Override
		public TupleExpression ofExpression(Expression x) {
			Preconditions.checkArgument(x.isTuple());
			return x.asTuple();
		}

		@Override
		public TupleExpression symbolicConstant(String name, boolean fresh) {
			return getExpressionManager().variable(name, getType(), fresh).asTuple();
		}

		@Override
		public TupleExpression toTupleExpression(TupleExpression Tuple) {
			return Tuple;
		}

		@Override
		public VariableExpression toVariable(TupleExpression x) {
			Preconditions.checkArgument(x.isVariable());
			return x.asVariable();
		}

		@Override
		public TupleExpression update(TupleExpression Tuple, int index,
		    Expression val) {
			return Tuple.update(index, val);
		}

		@Override
		public TupleExpression variable(String name, boolean fresh) {
			return variable(name, fresh);
		}

		@Override
		public TupleExpression boundVar(String name, boolean fresh) {
			return boundVar(name, fresh);
		}

		@Override
		public TupleExpression boundExpression(String name, int index,
		    boolean fresh) {
			return boundExpression(name, index, fresh);
		}

		@Override
		public TupleExpression variable(String name, IRType iType, boolean fresh) {
			return getExpressionManager().variable(name, getType(), fresh).asTuple();
		}

		@Override
		public TupleExpression boundVar(String name, IRType iType, boolean fresh) {
			return getExpressionManager().boundVar(name, getType(), fresh).asTuple();
		}

		@Override
		public TupleExpression boundExpression(String name, int index, IRType iType,
		    boolean fresh) {
			return getExpressionManager().boundExpression(name, index, getType(),
			    fresh).asTuple();
		}
	}
}
