package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.RationalExpression;

public interface RationalType extends Type, ComparableType, AddableType,
    MultiplicativeType, ScalarType {
  RationalExpression constant(int numerator, int denominator);
  
  @Override
  RationalExpression variable(String name, boolean fresh) ;
  
  @Override
  RationalExpression boundVar(String name, boolean fresh);
  
  @Override
  RationalExpression boundExpression(String name, int index, boolean fresh);
}
