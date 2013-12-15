package edu.nyu.cascade.fds;

import java.math.BigInteger;
import java.util.List;

import com.google.common.collect.Lists;
import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;

import edu.nyu.cascade.ir.expr.IntegerEncoding;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.Type;

public class TemporalIntegerEncoding<T extends Expression> extends
    TemporalTypeEncoding<T> implements
    IntegerEncoding<StateExpression> {
  public static <T extends Expression> TemporalIntegerEncoding<T> create(
      IntegerEncoding<T> baseEncoding, StateExpression.Factory stateExprFactory) {
    return new TemporalIntegerEncoding<T>(baseEncoding, stateExprFactory);
  }
  
  private final IntegerEncoding<T> baseEncoding;
  private final StateExpression.Factory stateExprFactory;

  @Inject
  private TemporalIntegerEncoding(@Assisted IntegerEncoding<T> baseEncoding,
      StateExpression.Factory stateExprFactory) {
    super(baseEncoding,stateExprFactory);
    this.baseEncoding = baseEncoding;
    this.stateExprFactory = stateExprFactory;
  }

  @Override
  public StateExpression bitwiseAnd(StateExpression a,
      StateExpression b) {
    return stateExprFactory.valueOf((Expression) baseEncoding.bitwiseAnd(
        baseEncoding.ofExpression(a.toExpression()), baseEncoding
            .ofExpression(b.toExpression())));
  }

  @Override
  public StateExpression constant(int c) {
    return stateExprFactory.valueOf((Expression) baseEncoding.constant(c));
  }
  
  @Override
  public StateExpression constant(long c) {
    return stateExprFactory.valueOf((Expression) baseEncoding.constant(c));
  }
  
  @Override
  public StateExpression constant(BigInteger c) {
    return stateExprFactory.valueOf((Expression) baseEncoding.constant(c));
  }

  @Override
  public StateExpression decr(StateExpression expr) {
    return stateExprFactory.valueOf((Expression) baseEncoding.decr(
        baseEncoding.ofExpression(expr.toExpression())));  }

  @Override
  public BooleanExpression distinct(Iterable<? extends StateExpression> exprs) {
    List<T> baseExprs = Lists.newArrayList();
    for( StateExpression e : exprs) {
      baseExprs.add( baseEncoding.ofExpression(e.toExpression()));
    }
    return baseEncoding.distinct(
        baseExprs); 
  }

  @Override
  public BooleanExpression greaterThan(StateExpression a,
      StateExpression b) {
    return baseEncoding.greaterThan(
        baseEncoding.ofExpression(a.toExpression()), baseEncoding
            .ofExpression(b.toExpression()));
  }
  
  @Override
  public BooleanExpression signedGreaterThan(StateExpression a,
      StateExpression b) {
    return baseEncoding.signedGreaterThan(
        baseEncoding.ofExpression(a.toExpression()), baseEncoding
            .ofExpression(b.toExpression()));
  }

  @Override
  public BooleanExpression greaterThanOrEqual(StateExpression a,
      StateExpression b) {
    return baseEncoding.greaterThanOrEqual(
        baseEncoding.ofExpression(a.toExpression()), baseEncoding
            .ofExpression(b.toExpression()));
  }
  
  @Override
  public BooleanExpression signedGreaterThanOrEqual(StateExpression a,
      StateExpression b) {
    return baseEncoding.signedGreaterThanOrEqual(
        baseEncoding.ofExpression(a.toExpression()), baseEncoding
            .ofExpression(b.toExpression()));
  }

  @Override
  public StateExpression ifThenElse(BooleanExpression b,
      StateExpression thenExpr, StateExpression elseExpr) {
    return stateExprFactory.valueOf((Expression) baseEncoding.ifThenElse(b,
        baseEncoding.ofExpression(thenExpr.toExpression()),
        baseEncoding.ofExpression(elseExpr.toExpression())));
  }

  @Override
  public StateExpression incr(StateExpression expr) {
    return stateExprFactory.valueOf((Expression) baseEncoding.incr(
        baseEncoding.ofExpression(expr.toExpression())));
  }

  @Override
  public BooleanExpression lessThan(StateExpression a,
      StateExpression b) {
    return baseEncoding.lessThan(
        baseEncoding.ofExpression(a.toExpression()), baseEncoding
            .ofExpression(b.toExpression()));
  }
  
  @Override
  public BooleanExpression signedLessThan(StateExpression a,
      StateExpression b) {
    return baseEncoding.signedLessThan(
        baseEncoding.ofExpression(a.toExpression()), baseEncoding
        .ofExpression(b.toExpression()));
  }

  @Override
  public BooleanExpression lessThanOrEqual(StateExpression a,
      StateExpression b) {
    return baseEncoding.lessThanOrEqual(
        baseEncoding.ofExpression(a.toExpression()), baseEncoding
            .ofExpression(b.toExpression()));
  }

  @Override
  public BooleanExpression signedLessThanOrEqual(StateExpression a,
      StateExpression b) {
    return baseEncoding.signedLessThanOrEqual(
        baseEncoding.ofExpression(a.toExpression()), baseEncoding
            .ofExpression(b.toExpression()));
  }

  @Override
  public StateExpression minus(StateExpression a, StateExpression b) {
    return stateExprFactory.valueOf((Expression) baseEncoding.minus(
        baseEncoding.ofExpression(a.toExpression()), baseEncoding
            .ofExpression(b.toExpression())));
  }

  @Override
  public StateExpression negate(StateExpression arg) {
    return stateExprFactory.valueOf((Expression) baseEncoding.negate(
        baseEncoding.ofExpression(arg.toExpression())));
  }

  @Override
  public BooleanExpression neq(StateExpression a, StateExpression b) {
    return baseEncoding.neq(
        baseEncoding.ofExpression(a.toExpression()), baseEncoding
            .ofExpression(b.toExpression()));
  }

  @Override
  public StateExpression ofBoolean(BooleanExpression b) {
    return stateExprFactory.valueOf((Expression) baseEncoding.ofBoolean(b));
  }
  
  @Override
  public StateExpression ofInteger(StateExpression a, int size) {
    return stateExprFactory.valueOf((Expression) baseEncoding.ofInteger(
    		baseEncoding.ofExpression(a), size));
  }

  @Override
  public StateExpression one() {
    return stateExprFactory.valueOf((Expression) baseEncoding.one());
  }

  @Override
  public StateExpression plus(Iterable<? extends StateExpression> args) {
    List<T> baseExprs = Lists.newArrayList();
    for( StateExpression e : args) {
      baseExprs.add( baseEncoding.ofExpression(e.toExpression()));
    }
    return stateExprFactory.valueOf((Expression) baseEncoding.plus(
        baseExprs)); 
  }

  @Override
  public StateExpression plus(StateExpression a, StateExpression b) {
    return stateExprFactory.valueOf((Expression) baseEncoding.plus(
        baseEncoding.ofExpression(a.toExpression()), baseEncoding
            .ofExpression(b.toExpression())));
  }

  @Override
  public StateExpression plus(StateExpression... args) {
    List<T> baseExprs = Lists.newArrayList();
    for( StateExpression e : args) {
      baseExprs.add( baseEncoding.ofExpression(e.toExpression()));
    }
    return stateExprFactory.valueOf((Expression) baseEncoding.distinct(
        baseExprs)); 
  }

  @Override
  public StateExpression times(StateExpression a, StateExpression b) {
    return stateExprFactory.valueOf((Expression) baseEncoding.times(
        baseEncoding.ofExpression(a.toExpression()), baseEncoding
            .ofExpression(b.toExpression())));
  } 
  
  @Override
  public StateExpression divide(StateExpression a, StateExpression b) {
    return stateExprFactory.valueOf((Expression) baseEncoding.divide(
        baseEncoding.ofExpression(a.toExpression()), baseEncoding
            .ofExpression(b.toExpression())));
  }
  
  @Override
  public StateExpression mod(StateExpression a, StateExpression b) {
    return stateExprFactory.valueOf((Expression) baseEncoding.mod(
        baseEncoding.ofExpression(a.toExpression()), baseEncoding
            .ofExpression(b.toExpression())));
  }
  
  @Override
  public BooleanExpression toBoolean(StateExpression expr) {
    return baseEncoding.toBoolean(
        baseEncoding.ofExpression(expr.toExpression()));
  }

  @Override
  public StateExpression unknown() {
    return stateExprFactory.valueOf((Expression) baseEncoding.unknown());
  }

  @Override
  public StateExpression zero() {
    return stateExprFactory.valueOf((Expression) baseEncoding.zero());
  }

  @Override
  public StateExpression unknown(Type type) {
    return stateExprFactory.valueOf((Expression) baseEncoding.unknown(type));
  }

	@Override
	public StateExpression uminus(StateExpression expr) {
		return stateExprFactory.valueOf((Expression) baseEncoding.uminus(
        baseEncoding.ofExpression(expr.toExpression())));
	}

	@Override
	public StateExpression lshift(StateExpression lhs, StateExpression rhs) {
		return stateExprFactory.valueOf((Expression) baseEncoding.lshift(
        baseEncoding.ofExpression(lhs.toExpression()), baseEncoding
            .ofExpression(rhs.toExpression())));
	}

	@Override
	public StateExpression rshift(StateExpression lhs, StateExpression rhs) {
		return stateExprFactory.valueOf((Expression) baseEncoding.rshift(
        baseEncoding.ofExpression(lhs.toExpression()), baseEncoding
            .ofExpression(rhs.toExpression())));
	}

	@Override
	public StateExpression rem(StateExpression lhs, StateExpression rhs) {
		return stateExprFactory.valueOf((Expression) baseEncoding.rem(
        baseEncoding.ofExpression(lhs.toExpression()), baseEncoding
            .ofExpression(rhs.toExpression())));
	}

	@Override
	public StateExpression signedRem(StateExpression lhs, StateExpression rhs) {
		return stateExprFactory.valueOf((Expression) baseEncoding.signedRem(
        baseEncoding.ofExpression(lhs.toExpression()), baseEncoding
            .ofExpression(rhs.toExpression())));
	}

	@Override
	public StateExpression signedDivide(StateExpression lhs, StateExpression rhs) {
		return stateExprFactory.valueOf((Expression) baseEncoding.signedDivide(
        baseEncoding.ofExpression(lhs.toExpression()), baseEncoding
            .ofExpression(rhs.toExpression())));
	}

	@Override
  public StateExpression variable(String name, Type type, boolean fresh) {
	  return stateExprFactory.valueOf((Expression) baseEncoding.variable(name, fresh));
  }
}
