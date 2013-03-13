package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.Expression;

public interface IntegerType extends Type, AddableType,
    ComparableType, MultiplicativeType {
  Expression mod(Expression left, Expression right);
}
