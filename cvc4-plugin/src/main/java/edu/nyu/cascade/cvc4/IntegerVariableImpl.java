package edu.nyu.cascade.cvc4;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.IntegerVariableExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public final class IntegerVariableImpl extends VariableExpressionImpl implements
    IntegerVariableExpression {
  static IntegerVariableImpl valueOf(ExpressionManagerImpl em, Expression e) {
    if (e instanceof IntegerVariableImpl && em.equals(e.getExpressionManager())) {
      return (IntegerVariableImpl) e;
    } else if (e instanceof VariableExpression) {
      VariableExpression e2 = (VariableExpression)e;
      return new IntegerVariableImpl(em, e2);
    } else {
      throw new IllegalArgumentException("Expression type: " + e.getClass());
    }
  }

  /** Create a new integer variable. */
  IntegerVariableImpl(ExpressionManagerImpl em, String name, boolean fresh) {
    super(em, name, em.integerType(), fresh);
  }

  /** Create a new variable of an integer subtype (e.g., a range type). */
  IntegerVariableImpl(ExpressionManagerImpl em, String name, Type type, boolean fresh) {
    super(em, name, type, fresh);
    Preconditions.checkArgument(type.isInteger());
  }

  /** Copy constructor. */
  IntegerVariableImpl(ExpressionManagerImpl em, VariableExpression x) {
    this(em, x.getName(), x.getType(), false);
  }
  
  @Override
  public RationalExpressionImpl castToRational() {
//     return getType().castToRational(this);
    throw new UnsupportedOperationException();
  }

  @Override
  public Kind getKind() {
    return Kind.VARIABLE;
  }

  @Override
  public IntegerTypeImpl getType() {
    return (IntegerTypeImpl) super.getType();
  }

  @Override
  public BooleanExpressionImpl greaterThan(Expression e) {
    return getType().gt(this, e);
  }

  @Override
  public BooleanExpressionImpl greaterThanOrEqual(Expression e) {
    return getType().geq(this, e);
  }

  @Override
  public BooleanExpression lessThan(Expression e) {
    return getType().lt(this, e);
  }

  @Override
  public BooleanExpression lessThanOrEqual(Expression e) {
    return getType().leq(this, e);
  }

  @Override
  public IntegerExpression minus(Expression e) {
    return getType().subtract(this, e);
  }

  @Override
  public IntegerExpression negate() {
    return getType().negate(this);
  }

  @Override
  public IntegerExpression plus(Expression e) {
    return getType().add(this, e);
  }

  @Override
  public IntegerExpression pow(Expression e) {
    return getType().pow(this, e);
  }

  @Override
  public IntegerExpression times(Expression e) {
    return getType().mult(this, e);
  }
  
  @Override
  public IntegerExpression divides(Expression e) {
    return getType().divide(this, e);
  }
  
  @Override
  public IntegerExpression mods(Expression e) {
    return getType().mod(this, e);
  }
}
