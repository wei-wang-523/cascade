package edu.nyu.cascade.prover;

import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.Selector;

public interface InductiveExpression extends Expression {
  Expression select(Selector selector);
  BooleanExpression test(Constructor constructor);
  @Override InductiveType getType();
}
