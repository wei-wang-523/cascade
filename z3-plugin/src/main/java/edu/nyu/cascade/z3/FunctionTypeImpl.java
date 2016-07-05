package edu.nyu.cascade.z3;

import com.google.common.base.Function;
import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.microsoft.z3.Expr;

import edu.nyu.cascade.prover.Expression;
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

		TypeImpl rangeType = exprManager.importType(range);

		return new FunctionTypeImpl(exprManager, argTypes1, rangeType);
	}

	static FunctionTypeImpl valueOf(ExpressionManagerImpl exprManager, Type t) {
		if (t instanceof FunctionDeclarator) {
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
	public String getName() {
		return "(" + Joiner.on(",").join(argTypes) + ") -> " + rangeType;
	}

	@Override
	ExpressionImpl createExpression(Expr res, Expression oldExpr,
			Iterable<? extends ExpressionImpl> children) {
		throw new UnsupportedOperationException();
	}

	@Override
	public String toString() {
		return getName();
	}
}