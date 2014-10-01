package edu.nyu.cascade.z3;

import edu.nyu.cascade.prover.UninterpretedExpression;

final class UninterpretedBoundExpressionImpl extends BoundExpressionImpl
    implements UninterpretedExpression {

	static UninterpretedBoundExpressionImpl create(ExpressionManagerImpl exprManager,
      String name, UninterpretedTypeImpl type, boolean fresh) {
    return new UninterpretedBoundExpressionImpl(exprManager, name, type, fresh);
  }

  private UninterpretedBoundExpressionImpl(ExpressionManagerImpl exprManager, String name,
      UninterpretedTypeImpl type, boolean fresh) {
    super(exprManager, name, type, fresh);
  }
  
	static UninterpretedBoundExpressionImpl create(ExpressionManagerImpl exprManager,
      String name, int index, UninterpretedTypeImpl type, boolean fresh) {
    return new UninterpretedBoundExpressionImpl(exprManager, name, index, type, fresh);
  }

  private UninterpretedBoundExpressionImpl(ExpressionManagerImpl exprManager, String name, int index,
      UninterpretedTypeImpl type, boolean fresh) {
    super(exprManager, name, index, type, fresh);
  }

  @Override
  public UninterpretedTypeImpl getType() {
    return (UninterpretedTypeImpl) super.getType();
  }
}
