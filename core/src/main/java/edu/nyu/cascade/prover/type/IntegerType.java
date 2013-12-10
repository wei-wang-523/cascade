package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.IntegerVariableExpression;

public interface IntegerType extends Type, AddableType,
    ComparableType, MultiplicativeType {
  Expression mod(Expression left, Expression right);
  
  IntegerVariableExpression variable(String name, boolean fresh);
  IntegerVariableExpression boundVariable(String name, boolean fresh);
}
