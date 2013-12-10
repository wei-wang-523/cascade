package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.RationalExpression;
import edu.nyu.cascade.prover.RationalVariableExpression;

public interface RationalType extends Type, ComparableType, AddableType,
    MultiplicativeType {
  RationalExpression constant(int numerator, int denominator);
  
  RationalVariableExpression variable(String name, boolean fresh) ;
  RationalVariableExpression boundVariable(String name, boolean fresh);
}
