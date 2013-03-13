package edu.nyu.cascade.cvc4;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.RationalVariableExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public class RationalBoundVariableImpl extends BoundVariableExpressionImpl
    implements RationalVariableExpression {
  public
  static RationalBoundVariableImpl valueOf(ExpressionManagerImpl em, Expression e) {
    if (e instanceof RationalBoundVariableImpl) {
      return (RationalBoundVariableImpl) e;
    } else if (e instanceof BoundVariableExpressionImpl) {
      BoundVariableExpressionImpl e2 = (BoundVariableExpressionImpl)e;
      return new RationalBoundVariableImpl(em,e2);
    } else {
      throw new IllegalArgumentException("Expression type: " + e.getClass());
    }
  }

  public static RationalBoundVariableImpl create(ExpressionManagerImpl em,
      String name, Type type, boolean fresh) {
    Preconditions.checkArgument(type.isRational());
    return new RationalBoundVariableImpl(em, name, type, fresh);
  }

  /** Copy constructor. */
  private RationalBoundVariableImpl(ExpressionManagerImpl em, VariableExpression x) {
    this(em, x.getName(), x.getType(), false);
  }

  /** Create a new rational variable. */
  public RationalBoundVariableImpl(ExpressionManagerImpl em, String name, boolean fresh) {
    super(em, name, em.rationalType(),fresh);
  }
  
  /** Create a new variable of a rational sub-type (e.g., a range type). */
  private RationalBoundVariableImpl(ExpressionManagerImpl em, String name, Type type, boolean fresh) {
    super(em, name, type, fresh);
  }

  @Override
  public RationalTypeImpl getType() {
    return getExpressionManager().rationalType();
  }

  @Override
  public RationalExpressionImpl divide(Expression e) {
    return getType().divide(this,e);
  }

  @Override
  public BooleanExpressionImpl gt(Expression e) {
    return getType().gt(this,e);
  }

  @Override
  public BooleanExpressionImpl geq(Expression e) {
    return getType().geq(this,e);
  }

  @Override
  public BooleanExpressionImpl lt(Expression e) {
    return getType().lt(this,e);
  }

  @Override
  public BooleanExpressionImpl leq(Expression e) {
    return getType().leq(this,e);
  }

  @Override
  public RationalExpressionImpl mult(Expression e) {
    return getType().mult(this,e);
  }

  @Override
  public RationalExpressionImpl pow(Expression exp) {
    return getType().pow(this,exp);
  }

  @Override
  public RationalExpressionImpl minus(Expression e) {
    return getType().subtract(this, e);
  }

  @Override
  public RationalExpressionImpl plus(Expression e) {
    return getType().add(this, e);
  }
}
