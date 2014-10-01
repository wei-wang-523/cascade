package edu.nyu.cascade.cvc4;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.Type;

final class ArrayBoundVariableImpl extends BoundVariableExpressionImpl implements
    ArrayExpression {

  ArrayBoundVariableImpl(ExpressionManagerImpl exprManager, String name, ArrayTypeImpl type, boolean fresh) {
    super(exprManager, name, type, fresh);
  }

  @Override
  public ArrayTypeImpl getType() {
    return (ArrayTypeImpl) super.getType();
  }

  @Override
  public Type getElementType() {
    return getType().getElementType();
  }

  @Override
  public Type getIndexType() {
    return getType().getIndexType();
  }

  @Override
  public ExpressionImpl index(Expression i) {
    return ArrayExpressionImpl.mkArrayIndex(getExpressionManager(), this, i);
  }

  @Override
  public ArrayExpressionImpl update(Expression i, Expression val) {
    return ArrayExpressionImpl.mkUpdate(getExpressionManager(), this, i, val);
  }
}
