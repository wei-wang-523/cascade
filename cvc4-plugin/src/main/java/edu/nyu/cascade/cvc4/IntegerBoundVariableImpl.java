package edu.nyu.cascade.cvc4;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.IntegerVariableExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public final class IntegerBoundVariableImpl extends BoundVariableExpressionImpl implements
    IntegerVariableExpression {
	
  protected static IntegerBoundVariableImpl valueOf(ExpressionManagerImpl em, Expression e) {
    if (e instanceof IntegerBoundVariableImpl && em.equals(e.getExpressionManager())) {
      return (IntegerBoundVariableImpl) e;
    } else if (e instanceof BoundVariableExpressionImpl) {
      BoundVariableExpressionImpl e2 = (BoundVariableExpressionImpl)e;
      return new IntegerBoundVariableImpl(em, e2);
    } else {
      throw new IllegalArgumentException("Expression type: " + e.getClass());
    }
  }
  
	protected static IntegerBoundVariableImpl create(
      ExpressionManagerImpl em, String name, boolean fresh) {
    return new IntegerBoundVariableImpl(em, name, fresh);
  }

  protected static IntegerBoundVariableImpl create(
      ExpressionManagerImpl exprManager, String name, IntegerTypeImpl type, boolean fresh) {
    return new IntegerBoundVariableImpl(exprManager, name, type, fresh);
  }

  /** Create a new integer variable. */
  private IntegerBoundVariableImpl(ExpressionManagerImpl em, String name, boolean fresh) {
    super(em, name, em.integerType(), fresh);
  }

  /** Create a new variable of an integer subtype (e.g., a range type). */
  private IntegerBoundVariableImpl(ExpressionManagerImpl em, String name, Type type, boolean fresh) {
    super(em, name, type, fresh);
    Preconditions.checkArgument(type.isInteger());
  }

  /** Copy constructor. */
  private IntegerBoundVariableImpl(ExpressionManagerImpl em, VariableExpression x) {
    this(em, x.getName(), x.getType(), false);
  }
  
  @Override
  public RationalExpressionImpl castToRational() {
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
