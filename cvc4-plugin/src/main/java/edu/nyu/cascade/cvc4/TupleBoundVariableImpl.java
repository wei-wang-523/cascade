package edu.nyu.cascade.cvc4;

import java.util.List;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.TupleVariableExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public final class TupleBoundVariableImpl extends BoundVariableExpressionImpl implements
    TupleVariableExpression {
  
  static  TupleBoundVariableImpl create(
      ExpressionManagerImpl exprManager, String name, List<TypeImpl> args, boolean fresh) {
    TupleTypeImpl type = exprManager.tupleType(args);

    return new TupleBoundVariableImpl(exprManager,name, type,fresh);
  }

  static  TupleBoundVariableImpl create(
      ExpressionManagerImpl exprManager, String name, TupleTypeImpl type, boolean fresh) {
    return new TupleBoundVariableImpl(exprManager,name, type, fresh);
  }

  private TupleBoundVariableImpl(ExpressionManagerImpl exprManager, String name, TupleTypeImpl type, boolean fresh) {
    super(exprManager, name, type, fresh);
  }
  
  static TupleBoundVariableImpl valueOf(ExpressionManagerImpl em, Expression e) {
    if (e instanceof TupleBoundVariableImpl && em.equals(e.getExpressionManager())) {
      return (TupleBoundVariableImpl) e;
    } else if (e instanceof BoundVariableExpressionImpl) {
      BoundVariableExpressionImpl e2 = (BoundVariableExpressionImpl)e;
      return new TupleBoundVariableImpl(em, e2);
    } else {
      throw new IllegalArgumentException("Expression type: " + e.getClass());
    }
  }

  /** Create a new integer variable. */
  TupleBoundVariableImpl(ExpressionManagerImpl em, String name, List<Type> typeArgs, boolean fresh) {
    super(em, name, em.tupleType(typeArgs), fresh);
  }

  /** Create a new variable of an integer subtype (e.g., a range type). */
  TupleBoundVariableImpl(ExpressionManagerImpl em, String name, Type type, boolean fresh) {
    super(em, name, type, fresh);
    Preconditions.checkArgument(type.isTuple());
  }

  /** Copy constructor. */
  TupleBoundVariableImpl(ExpressionManagerImpl em, VariableExpression x) {
    this(em, x.getName(), x.getType(), false);
  }

  @Override
  public Kind getKind() {
    return Kind.VARIABLE;
  }

  @Override
  public TupleTypeImpl getType() {
    return (TupleTypeImpl) super.getType();
  }

  @Override
  public Expression index(int i) {
    return TupleExpressionImpl.mkTupleIndex(getExpressionManager(), this, i);
  }

  @Override
  public int size() {
    return getType().size();
  }

  @Override
  public TupleExpression update(int index, Expression val) {
    return TupleExpressionImpl.mkUpdate(getExpressionManager(), this, index, val);
  }
}
