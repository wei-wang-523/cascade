package edu.nyu.cascade.cvc4;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.InductiveExpression;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.Selector;

final class InductiveBoundVariableImpl extends BoundVariableExpressionImpl
    implements InductiveExpression {
	
	InductiveBoundVariableImpl(ExpressionManagerImpl exprManager, String name,
      InductiveTypeImpl type, boolean fresh) {
    super(exprManager, name, type, true);
  }

  @Override
  public InductiveTypeImpl getType() {
    return (InductiveTypeImpl) super.getType();
  }

  @Override
  public SelectExpressionImpl select(Selector selector) {
    return SelectExpressionImpl.create(getExpressionManager(), selector, this);
  }

  @Override
  public BooleanExpression test(Constructor constructor) {
    return TestExpressionImpl.create(getExpressionManager(), constructor, this);
  }
}
