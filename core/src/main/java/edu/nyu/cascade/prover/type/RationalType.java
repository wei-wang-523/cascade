package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.RationalExpression;

public interface RationalType extends Type, ComparableType, AddableType,
    MultiplicativeType {
  RationalExpression constant(int numerator, int denominator);

  RationalExpression divide(Expression a, Expression b);

  RationalExpression one();

  RationalExpression zero();
}
