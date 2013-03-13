package edu.nyu.cascade.cvc4;

import edu.nyu.cascade.prover.VariableExpression;

public final class BooleanBoundVariableImpl extends BoundVariableExpressionImpl implements
    VariableExpression {

  BooleanBoundVariableImpl(ExpressionManagerImpl em, String name, boolean fresh) {
    super(em, name, em.booleanType(), fresh);
  }

  @Override
  public BooleanTypeImpl getType() {
    return (BooleanTypeImpl) super.getType();
  }
}
