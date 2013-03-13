package edu.nyu.cascade.z3;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.InductiveExpression;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.Selector;

public class InductiveVariableImpl extends VariableExpressionImpl
    implements InductiveExpression {
  public static InductiveVariableImpl create(ExpressionManagerImpl exprManager,
      String name, InductiveTypeImpl type, boolean fresh) {
    return new InductiveVariableImpl(exprManager, name, type, fresh);
  }

  private InductiveVariableImpl(ExpressionManagerImpl exprManager, String name,
      InductiveTypeImpl type, boolean fresh) {
    super(exprManager, name, type, true);
  }

  @Override
  public InductiveTypeImpl getType() {
    return (InductiveTypeImpl) super.getType();
  }

  @Override
  public Expression select(Selector selector) {
    return selector.apply(this);
  }

  @Override
  public BooleanExpression test(Constructor constructor) {
    return getType().test(constructor, this);
  }
}
