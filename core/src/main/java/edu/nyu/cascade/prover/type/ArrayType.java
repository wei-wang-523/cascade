package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;

public interface ArrayType extends Type, ScalarType {
  Type getIndexType();
  Type getElementType();
  
  @Override
  ArrayExpression variable(String name, boolean fresh) ;
  
  @Override
  ArrayExpression boundVar(String name, boolean fresh);
  
  @Override
  ArrayExpression boundExpression(String name, int index, boolean fresh);
  
  Expression index(Expression array, Expression index);
  ArrayExpression update(Expression array, Expression index, Expression value);
	ArrayExpression storeAll(Expression expr, ArrayType type);
}
