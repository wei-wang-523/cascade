package edu.nyu.cascade.z3;

import java.util.List;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.TupleVariableExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public final class TupleVariableImpl extends VariableExpressionImpl implements
    TupleVariableExpression {
  
  static  TupleVariableImpl create(
      ExpressionManagerImpl exprManager, String tname, String name, List<TypeImpl> args, boolean fresh) {
    TupleTypeImpl type = exprManager.tupleType(tname, args);

    return new TupleVariableImpl(exprManager,name, type,fresh);
  }

  static  TupleVariableImpl create(
      ExpressionManagerImpl exprManager, String name, TupleTypeImpl type, boolean fresh) {
    return new TupleVariableImpl(exprManager,name, type, fresh);
  }

  private TupleVariableImpl(ExpressionManagerImpl exprManager, String name, TupleTypeImpl type, boolean fresh) {
    super(exprManager, name, type, fresh);
  }
  
  static TupleVariableImpl valueOf(ExpressionManagerImpl em, Expression e) {
    if (e instanceof TupleVariableImpl && em.equals(e.getExpressionManager())) {
      return (TupleVariableImpl) e;
    } else if (e instanceof VariableExpression) {
      VariableExpression e2 = (VariableExpression)e;
      return new TupleVariableImpl(em, e2);
    } else {
      throw new IllegalArgumentException("Expression type: " + e.getClass());
    }
  }

  /** Create a new integer variable. */
  TupleVariableImpl(ExpressionManagerImpl em, String tname, String name, List<Type> typeArgs, boolean fresh) {
    super(em, name, em.tupleType(tname, typeArgs), fresh);
  }

  /** Create a new variable of an integer subtype (e.g., a range type). */
  TupleVariableImpl(ExpressionManagerImpl em, String name, Type type, boolean fresh) {
    super(em, name, type, fresh);
    Preconditions.checkArgument(type.isTuple());
  }

  /** Copy constructor. */
  TupleVariableImpl(ExpressionManagerImpl em, VariableExpression x) {
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
    return getType().index(this, i);
  }

  @Override
  public int size() {
    return getType().size();
  }

  @Override
  public TupleExpression update(int index, Expression val) {
    return getType().update(this, index, val);
  }
}