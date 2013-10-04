package edu.nyu.cascade.z3;

import java.util.List;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.RecordVariableExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public final class RecordVariableImpl extends VariableExpressionImpl implements
    RecordVariableExpression {
  
  static  RecordVariableImpl create(
      ExpressionManagerImpl exprManager, String tname, List<String> elemNames, List<TypeImpl> elemTypes, boolean fresh) {
    RecordTypeImpl type = exprManager.recordType(tname, elemNames, elemTypes);

    return new RecordVariableImpl(exprManager, tname, type, fresh);
  }

  static  RecordVariableImpl create(
      ExpressionManagerImpl exprManager, String name, TypeImpl type, boolean fresh) {
    return new RecordVariableImpl(exprManager,name, type, fresh);
  }

  private RecordVariableImpl(ExpressionManagerImpl exprManager, String name, RecordTypeImpl type, boolean fresh) {
    super(exprManager, name, type, fresh);
  }
  
  static RecordVariableImpl valueOf(ExpressionManagerImpl em, Expression e) {
    if (e instanceof RecordVariableImpl && em.equals(e.getExpressionManager())) {
      return (RecordVariableImpl) e;
    } else if (e instanceof VariableExpression) {
      VariableExpression e2 = (VariableExpression)e;
      return new RecordVariableImpl(em, e2);
    } else {
      throw new IllegalArgumentException("Expression type: " + e.getClass());
    }
  }

  /** Create a new integer variable. */
  RecordVariableImpl(ExpressionManagerImpl em, String tname, List<String> elemNames, List<Type> elemTypes, boolean fresh) {
    super(em, tname, em.recordType(tname, elemNames, elemTypes), fresh);
  }

  /** Create a new variable of an integer subtype (e.g., a range type). */
  RecordVariableImpl(ExpressionManagerImpl em, String name, Type type, boolean fresh) {
    super(em, name, type, fresh);
    Preconditions.checkArgument(type.isRecord());
  }

  /** Copy constructor. */
  RecordVariableImpl(ExpressionManagerImpl em, VariableExpression x) {
    this(em, x.getName(), x.getType(), false);
  }

  @Override
  public Kind getKind() {
    return Kind.VARIABLE;
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
