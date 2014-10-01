package edu.nyu.cascade.z3;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.type.Type;

final class RecordVariableImpl extends VariableExpressionImpl implements RecordExpression {

  static  RecordVariableImpl create(
      ExpressionManagerImpl exprManager, String name, TypeImpl type, boolean fresh) {
    return new RecordVariableImpl(exprManager,name, type, fresh);
  }

  /** Create a new variable of an integer subtype (e.g., a range type). */
  private RecordVariableImpl(ExpressionManagerImpl em, String name, Type type, boolean fresh) {
    super(em, name, type, fresh);
    Preconditions.checkArgument(type.isRecord());
  }

  @Override
  public RecordTypeImpl getType() {
    return (RecordTypeImpl) super.getType();
  }
  
  @Override
  public Expression select(String name) {
    return select(name);
  }

  @Override
  public RecordExpression update(String name, Expression val) {
    return update(name, val);
  }
}
