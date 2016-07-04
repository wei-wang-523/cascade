package edu.nyu.cascade.prover;

import edu.nyu.cascade.prover.type.TupleType;

public interface TupleExpression extends Expression {
	Expression index(int i);

	int size();

	TupleExpression update(int index, Expression val);

	@Override
	TupleType getType();
}
