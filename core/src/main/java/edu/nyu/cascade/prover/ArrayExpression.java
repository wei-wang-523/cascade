package edu.nyu.cascade.prover;

import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

public interface ArrayExpression extends Expression {
  Type getIndexType();

  Type getElementType();
  
  @Override
  ArrayType getType();

  Expression index(Expression i);

  ArrayExpression update(Expression i, Expression val);
}
