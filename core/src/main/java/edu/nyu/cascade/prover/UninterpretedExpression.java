package edu.nyu.cascade.prover;

import edu.nyu.cascade.prover.type.UninterpretedType;

public interface UninterpretedExpression extends Expression {
  @Override UninterpretedType getType();
}
