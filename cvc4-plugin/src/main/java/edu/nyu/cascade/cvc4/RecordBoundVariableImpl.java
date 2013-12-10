package edu.nyu.cascade.cvc4;

import java.util.List;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.RecordVariableExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public final class RecordBoundVariableImpl extends BoundVariableExpressionImpl implements
    RecordVariableExpression {
  
	protected static RecordBoundVariableImpl create(
      ExpressionManagerImpl exprManager, String name, String tname, 
      List<String> elemNames, List<TypeImpl> elemTypes, boolean fresh) {
    RecordTypeImpl type = exprManager.recordType(tname, elemNames, elemTypes);
    return new RecordBoundVariableImpl(exprManager,name, type,fresh);
  }

  protected static RecordBoundVariableImpl create(
      ExpressionManagerImpl exprManager, String name, RecordTypeImpl type, boolean fresh) {
    return new RecordBoundVariableImpl(exprManager,name, type, fresh);
  }

  protected static RecordBoundVariableImpl valueOf(ExpressionManagerImpl em, Expression e) {
    if (e instanceof RecordBoundVariableImpl && em.equals(e.getExpressionManager())) {
      return (RecordBoundVariableImpl) e;
    } else if (e instanceof BoundVariableExpressionImpl) {
      BoundVariableExpressionImpl e2 = (BoundVariableExpressionImpl)e;
      return new RecordBoundVariableImpl(em, e2);
    } else {
      throw new IllegalArgumentException("Expression type: " + e.getClass());
    }
  }

  private RecordBoundVariableImpl(ExpressionManagerImpl exprManager, String name, RecordTypeImpl type, boolean fresh) {
	  super(exprManager, name, type, fresh);
	}

	private RecordBoundVariableImpl(ExpressionManagerImpl em, String name, String tname,
      List<String> elemNames, List<Type> elemTypes, boolean fresh) {
    super(em, name, em.recordType(tname, elemNames, elemTypes), fresh);
  }
  
  private RecordBoundVariableImpl(ExpressionManagerImpl em, String name, Type type, boolean fresh) {
    super(em, name, type, fresh);
    Preconditions.checkArgument(type.isRecord());
  }

  /** Copy constructor. */
  private RecordBoundVariableImpl(ExpressionManagerImpl em, VariableExpression x) {
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
  public Expression select(String field) {
    return RecordExpressionImpl.mkRecordIndex(getExpressionManager(), this, field);
  }

  @Override
  public RecordExpression update(String field, Expression val) {
    return RecordExpressionImpl.mkUpdate(getExpressionManager(), this, field, val);
  }
}
