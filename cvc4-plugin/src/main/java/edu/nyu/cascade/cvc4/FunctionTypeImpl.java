package edu.nyu.cascade.cvc4;

import com.google.common.base.Function;
import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.vectorType;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.Expression.Kind;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Type;

final class FunctionTypeImpl extends TypeImpl implements FunctionType {

	static FunctionTypeImpl create(final ExpressionManagerImpl exprManager,
			Iterable<? extends Type> argTypes, Type range) {
		Iterable<TypeImpl> argTypes1 = Iterables.transform(argTypes,
				new Function<Type, TypeImpl>() {
					@Override
					public TypeImpl apply(Type t) {
						return exprManager.importType(t);
					}
				});
		return new FunctionTypeImpl(exprManager, argTypes1,
				exprManager.importType(range));
	}

	static FunctionTypeImpl valueOf(ExpressionManagerImpl exprManager, Type t) {
		if (t instanceof FunctionTypeImpl) {
			return (FunctionTypeImpl) t;
		} else {
			return create(exprManager, ((FunctionType) t).getArgTypes(),
					((FunctionType) t).getRangeType());
		}
	}

	private final ImmutableList<TypeImpl> argTypes;
	private final TypeImpl rangeType;

	private FunctionTypeImpl(final ExpressionManagerImpl exprManager,
			Iterable<? extends TypeImpl> argTypes, TypeImpl range) {
		super(exprManager);
		this.argTypes = ImmutableList.copyOf(argTypes);
		this.rangeType = range;
		try {
			vectorType argTypes1 = new vectorType();
			for (TypeImpl argType : argTypes) {
				argTypes1.add(exprManager.toCvc4Type(argType));
			}
			edu.nyu.acsys.CVC4.Type rangeType1 = exprManager.toCvc4Type(rangeType);
			setCVC4Type(exprManager.getTheoremProver().getCvc4ExprManager()
					.mkFunctionType(argTypes1, rangeType1));
		} catch (Exception e) {
			throw new TheoremProverException(e);
		}
	}

	@Override
	public String getName() {
		return "(" + Joiner.on(",").join(argTypes) + ") -> " + rangeType.getName();
	}

	@Override
	public Type getArgTypeAtIndex(int index) {
		return argTypes.get(index);
	}

	@Override
	public ImmutableList<? extends Type> getArgTypes() {
		return argTypes;
	}

	@Override
	public int getArity() {
		return argTypes.size();
	}

	@Override
	public Type getRangeType() {
		return rangeType;
	}

	@Override
	public DomainType getDomainType() {
		return DomainType.FUNCTION;
	}

	@Override
	FunctionExpressionImpl createExpression(Expr res, Expression e, Kind kind,
			Iterable<ExpressionImpl> children) {
		Preconditions.checkArgument(e.isFunction());
		return FunctionExpressionImpl.create(getExpressionManager(), kind, res,
				e.getType().asFunction(), children);
	}
}
