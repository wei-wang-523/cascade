package edu.nyu.cascade.cvc4;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.ArrayVariableExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.Type;

public final class ArrayBoundVariableImpl extends BoundVariableExpressionImpl implements
    ArrayVariableExpression {

  static  ArrayBoundVariableImpl create(
      ExpressionManagerImpl exprManager, String name, TypeImpl indexType, TypeImpl elementType, boolean fresh) {
    Preconditions.checkArgument(indexType.getExpressionManager().equals(
        elementType.getExpressionManager()));
    ArrayTypeImpl type = exprManager.arrayType(indexType, elementType);

    return new ArrayBoundVariableImpl(exprManager,name, type,fresh);
  }

  static  ArrayBoundVariableImpl create(
      ExpressionManagerImpl exprManager, String name, ArrayTypeImpl type, boolean fresh) {
    return new ArrayBoundVariableImpl(exprManager,name, type, fresh);
  }

  private ArrayBoundVariableImpl(ExpressionManagerImpl exprManager, String name, ArrayTypeImpl type, boolean fresh) {
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