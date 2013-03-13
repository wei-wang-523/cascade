package edu.nyu.cascade.fds;

import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;

import edu.nyu.cascade.ir.expr.RationalEncoding;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public class TemporalRationalEncoding<T extends Expression> extends TemporalTypeEncoding<T> 
  implements RationalEncoding<StateExpression> {
  public static <T extends Expression> TemporalRationalEncoding<T> create(
      RationalEncoding<T> baseEncoding, StateExpression.Factory stateExprFactory) {
    return new TemporalRationalEncoding<T>(baseEncoding, stateExprFactory);
  }
  
  private final RationalEncoding<T> baseEncoding;
  private final StateExpression.Factory stateExprFactory;

  @Inject
  private TemporalRationalEncoding(@Assisted RationalEncoding<T> baseEncoding,
      StateExpression.Factory stateExprFactory) {
    super(baseEncoding,stateExprFactory);
    this.baseEncoding = baseEncoding;
    this.stateExprFactory = stateExprFactory;
  }

  @Override
  public StateExpression constant(int numerator, int denominator) {
    return stateExprFactory.valueOf((Expression) baseEncoding.constant(numerator, denominator));
  }
  
  @Override
  public BooleanExpression gt(StateExpression lhs, StateExpression rhs) {
    return baseEncoding.gt(baseEncoding.ofExpression(lhs.toExpression()), 
                           baseEncoding.ofExpression(rhs.toExpression()));
  }

  @Override
  public BooleanExpression geq(StateExpression lhs, StateExpression rhs) {
    return baseEncoding.geq(baseEncoding.ofExpression(lhs.toExpression()), 
                            baseEncoding.ofExpression(rhs.toExpression()));
  }
  
  @Override
  public BooleanExpression lt(StateExpression lhs, StateExpression rhs) {
    return baseEncoding.lt(baseEncoding.ofExpression(lhs.toExpression()), 
                            baseEncoding.ofExpression(rhs.toExpression()));
  }

  @Override
  public BooleanExpression leq(StateExpression lhs, StateExpression rhs) {
    return baseEncoding.leq(baseEncoding.ofExpression(lhs.toExpression()), 
                            baseEncoding.ofExpression(rhs.toExpression()));
  }
  
  @Override
  public StateExpression plus(StateExpression a, StateExpression b) {
    return stateExprFactory.valueOf((Expression) baseEncoding.plus(
                            baseEncoding.ofExpression(a.toExpression()), 
                            baseEncoding.ofExpression(b.toExpression())));
  }
  
  @Override
  public StateExpression minus(StateExpression a, StateExpression b) {
    return stateExprFactory.valueOf((Expression) baseEncoding.minus(
                            baseEncoding.ofExpression(a.toExpression()), 
                            baseEncoding.ofExpression(b.toExpression())));
  }
  
  @Override
  public StateExpression mult(StateExpression a, StateExpression b) {
    return stateExprFactory.valueOf((Expression) baseEncoding.mult(
                            baseEncoding.ofExpression(a.toExpression()),
                            baseEncoding.ofExpression(b.toExpression())));
  }
  
  @Override
  public StateExpression divide(StateExpression a, StateExpression b) {
    return stateExprFactory.valueOf((Expression) baseEncoding.divide(
                            baseEncoding.ofExpression(a.toExpression()),
                            baseEncoding.ofExpression(b.toExpression())));
  }
  
  @Override
  public StateExpression pow(StateExpression a, StateExpression b) {
    return stateExprFactory.valueOf((Expression) baseEncoding.pow(
                            baseEncoding.ofExpression(a.toExpression()),
                            baseEncoding.ofExpression(b.toExpression())));
  }

  @Override
  public StateExpression one() {
    return stateExprFactory.valueOf((Expression) baseEncoding.one());
  }

  @Override
  public StateExpression zero() {
    return stateExprFactory.valueOf((Expression) baseEncoding.zero());
  }
}
