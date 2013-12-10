package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.ArrayVariableExpression;
import edu.nyu.cascade.prover.Expression;

public interface ArrayType extends Type {
  Type getIndexType();
  Type getElementType();
  ArrayVariableExpression variable(String name, boolean fresh) ;
  ArrayVariableExpression boundVariable(String name, boolean fresh);
  
  Expression index(Expression array, Expression index);
  ArrayExpression update(Expression array, Expression index, Expression value);
	ArrayExpression storeAll(Expression expr, ArrayType type);
}
