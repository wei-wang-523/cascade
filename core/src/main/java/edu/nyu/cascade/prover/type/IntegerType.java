package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.IntegerExpression;

public interface IntegerType
		extends Type, AddableType, ComparableType, MultiplicativeType, ScalarType {
	Expression mod(Expression left, Expression right);

	@Override
	IntegerExpression variable(String name, boolean fresh);

	@Override
	IntegerExpression boundVar(String name, boolean fresh);

	@Override
	IntegerExpression boundExpression(String name, int index, boolean fresh);
}
