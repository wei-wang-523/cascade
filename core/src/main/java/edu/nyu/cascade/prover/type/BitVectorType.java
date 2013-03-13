package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BitVectorVariableExpression;
import edu.nyu.cascade.prover.Expression;

public interface BitVectorType extends Type, ComparableType {
  BitVectorExpression add(int size, Expression a, Expression b);

  BitVectorExpression add(int size, Expression first, Expression... rest);

  BitVectorExpression add(int size, Iterable<? extends Expression> args);

  BitVectorExpression bitwiseAnd(Expression a, Expression b);

  BitVectorExpression bitwiseNand(Expression a, Expression b);

  BitVectorExpression bitwiseNor(Expression a, Expression b);

  BitVectorExpression bitwiseNot(Expression a);

  BitVectorExpression bitwiseOr(Expression a, Expression b);

  BitVectorExpression bitwiseXnor(Expression a, Expression b);

  BitVectorExpression bitwiseXor(Expression a, Expression b);

  BitVectorExpression concat(Expression a, Expression b);

  BitVectorExpression constant(int size, int val);

  BitVectorExpression constant(String rep);

  BitVectorExpression extract(Expression a, int i, int j);

  BitVectorExpression mult(int size, Expression a, Expression b);

  BitVectorExpression subtract(Expression a, Expression b);
  
  BitVectorExpression lshift(Expression a, Expression b);
  
  BitVectorExpression rshift(Expression a, Expression b);

  BitVectorVariableExpression variable(String name, boolean fresh);

  BitVectorExpression zero(int size);
  
  int getSize();
}
