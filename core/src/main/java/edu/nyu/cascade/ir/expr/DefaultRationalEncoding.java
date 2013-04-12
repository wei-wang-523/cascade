package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.RationalExpression;

public class DefaultRationalEncoding extends
    AbstractTypeEncoding<RationalExpression> implements
    RationalEncoding<RationalExpression> {
//  private static final String UNKNOWN_VARIABLE_NAME = "int_encoding_unknown";

  public DefaultRationalEncoding(ExpressionManager exprManager) {
    super(exprManager, exprManager.rationalType());
  }

  @Override
  public RationalExpression constant(int numerator, int denominator) {
    return getExpressionManager().rationalConstant(numerator, denominator);
  }
  
  @Override
  public BooleanExpression gt(RationalExpression lhs,
      RationalExpression rhs) {
    return lhs.gt(rhs);
  }

  @Override
  public BooleanExpression geq(RationalExpression lhs,
      RationalExpression rhs) {
    return lhs.geq(rhs);
  }
  
  @Override
  public BooleanExpression lt(RationalExpression lhs, RationalExpression rhs) {
    return lhs.lt(rhs);
  }

  @Override
  public BooleanExpression leq(RationalExpression lhs,
      RationalExpression rhs) {
    return lhs.leq(rhs);
  }

  @Override
  public RationalExpression plus(RationalExpression lhs, RationalExpression rhs) {
    return lhs.plus(rhs);
  }
  
  @Override
  public RationalExpression minus(RationalExpression lhs, RationalExpression rhs) {
    return lhs.minus(rhs);
  }
  
  @Override
  public RationalExpression mult(RationalExpression lhs, RationalExpression rhs) {
    return lhs.mult(rhs);
  }
  
  @Override
  public RationalExpression divide(RationalExpression lhs, RationalExpression rhs) {
    return lhs.divide(rhs);
  }
  
  @Override
  public RationalExpression pow(RationalExpression lhs, RationalExpression rhs) {
    return lhs.pow(rhs);
  }
  
  @Override
  public RationalExpression ofExpression(Expression x) {
    Preconditions.checkArgument(x.isRational());
    return x.asRationalExpression();
  }

  @Override
  public RationalExpression one() {
    return getExpressionManager().one().asRationalExpression();
  }

  @Override
  public RationalExpression zero() {
    return getExpressionManager().zero().asRationalExpression();
  }
}
