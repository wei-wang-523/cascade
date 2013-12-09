package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.RationalExpression;

public interface RationalType extends Type, ComparableType, AddableType,
    MultiplicativeType {
  RationalExpression constant(int numerator, int denominator);
}
