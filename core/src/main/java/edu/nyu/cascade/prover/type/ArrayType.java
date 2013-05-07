package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.ArrayVariableExpression;

public interface ArrayType extends Type {
  Type getIndexType();
  Type getElementType();
  ArrayVariableExpression variable(String name, boolean fresh) ;
}
