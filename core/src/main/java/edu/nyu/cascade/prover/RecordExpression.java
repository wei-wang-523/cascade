package edu.nyu.cascade.prover;

import edu.nyu.cascade.prover.type.RecordType;

public interface RecordExpression extends Expression {
	Expression select(String name);

	RecordExpression update(String name, Expression val);

	@Override
	RecordType getType();
}
