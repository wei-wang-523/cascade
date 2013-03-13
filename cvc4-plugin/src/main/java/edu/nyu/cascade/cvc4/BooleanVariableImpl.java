package edu.nyu.cascade.cvc4;

import edu.nyu.cascade.prover.VariableExpression;

public final class BooleanVariableImpl extends VariableExpressionImpl implements
    VariableExpression {

  BooleanVariableImpl(ExpressionManagerImpl em, String name, boolean fresh) {
    super(em, name, em.booleanType(), fresh);
  }

  @Override
  public BooleanTypeImpl getType() {
    return (BooleanTypeImpl) super.getType();
  }
}
