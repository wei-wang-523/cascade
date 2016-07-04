package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.Expression;

public interface ScalarType extends Type {
	Expression variable(String name, boolean fresh);

	Expression boundVar(String name, boolean fresh);

	Expression boundExpression(String name, int index, boolean fresh);
}
