package edu.nyu.cascade.fds;

import java.math.BigInteger;
import java.util.Arrays;

import com.google.common.base.Preconditions;
import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;

import edu.nyu.cascade.ir.expr.AbstractTypeEncoding;
import edu.nyu.cascade.ir.expr.IntegerEncoding;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;

public class StateExpressionIntegerEncoding extends
    AbstractTypeEncoding<StateExpression> implements
    IntegerEncoding<StateExpression> {
  
  private final StateExpression.Factory exprFactory;
  
  @Inject
  public StateExpressionIntegerEncoding(
      @Assisted ExpressionManager exprManager,
      StateExpression.Factory exprFactory) {
    super(exprManager,exprManager.integerType());
    this.exprFactory = exprFactory;
  }
  
  @Override
  public IntegerStateExpression bitwiseAnd(
      StateExpression a, StateExpression b)
       {
    throw new UnsupportedOperationException();
  }
  
  private IntegerStateExpression wrap(
      Expression expression) {
    return exprFactory.valueOf(expression).asIntegerExpression();
  }
  
  @Override
  public IntegerStateExpression decr(StateExpression expr)
       {
    return wrap(expr.asIntegerExpression().minus(one()));
  }

  @Override
  public StateProperty distinct(
      Iterable<? extends StateExpression> exprs) {
    return exprFactory.valueOf( getExpressionManager().distinct(exprs) ).asStateProperty();
  }

  @Override
  public StateProperty eq(StateExpression lhs,
      StateExpression rhs)  {
    return lhs.eq(rhs);
  }

  @Override
  public StateProperty greaterThan(StateExpression lhs,
      StateExpression rhs)  {
    return lhs.asIntegerExpression().greaterThan(rhs);
  }
  
  @Override
  public StateProperty signedGreaterThan(StateExpression lhs,
      StateExpression rhs)  {
    return lhs.asIntegerExpression().greaterThan(rhs);
  }

  @Override
  public StateProperty greaterThanOrEqual(StateExpression lhs,
      StateExpression rhs)  {
    return lhs.asIntegerExpression().greaterThanOrEqual(rhs);
  }
  
  @Override
  public StateProperty signedGreaterThanOrEqual(StateExpression lhs,
      StateExpression rhs)  {
    return lhs.asIntegerExpression().greaterThanOrEqual(rhs);
  }

  @Override
  public IntegerStateExpression incr(StateExpression expr)
       {
    return expr.asIntegerExpression().plus(one());
  }

  @Override
  public IntegerStateExpression constant(int c) {
    return wrap(getExpressionManager().constant(c));
  }
  
	@Override
	public StateExpression constant(long c) {
		return wrap(getExpressionManager().constant(c));
	}
	
	@Override
	public StateExpression constant(BigInteger c) {
		return wrap(getExpressionManager().constant(c));
	}

  @Override
  public StateProperty lessThan(StateExpression lhs,
      StateExpression rhs)  {
    return lhs.asIntegerExpression().lessThan(rhs);
  }
  
  @Override
  public BooleanExpression signedLessThan(StateExpression lhs,
      StateExpression rhs) {
    return lhs.asIntegerExpression().lessThan(rhs);
  }

  @Override
  public StateProperty lessThanOrEqual(StateExpression lhs,
      StateExpression rhs)  {
    return lhs.asIntegerExpression().lessThanOrEqual(rhs);
  }
  
  @Override
  public BooleanExpression signedLessThanOrEqual(StateExpression lhs,
      StateExpression rhs) {
    return lhs.asIntegerExpression().lessThanOrEqual(rhs);
  }

  @Override
  public IntegerStateExpression minus(StateExpression lhs,
      StateExpression rhs)  {
    return lhs.asIntegerExpression().minus(rhs);
  }

  @Override
  public IntegerStateExpression negate(StateExpression arg)
       {
    return arg.asIntegerExpression().negate();
  }

  @Override
  public StateProperty neq(StateExpression lhs,
      StateExpression rhs)  {
    return lhs.neq(rhs);
  }

  @Override
  public IntegerStateExpression one()  {
    return wrap(getExpressionManager().one());
  }

  @Override
  public IntegerStateExpression plus(StateExpression... args)
       {
    return plus(Arrays.asList(args));
  }

  @Override
  public IntegerStateExpression plus(StateExpression lhs,
      StateExpression rhs)  {
    return wrap(lhs.asIntegerExpression().plus(rhs));
  }

  @Override
  public IntegerStateExpression plus(
      Iterable<? extends StateExpression> args)
       {
    return wrap(getExpressionManager().plus(args));
  }
  
  @Override
  public IntegerStateExpression times(StateExpression lhs,
      StateExpression rhs)  {
    return wrap(lhs.asIntegerExpression().times(rhs));
  }
  
  @Override
  public IntegerStateExpression divide(StateExpression lhs,
      StateExpression rhs)  {
    return wrap(lhs.asIntegerExpression().divides(rhs));
  }
  
  @Override
  public IntegerStateExpression mod(StateExpression lhs,
      StateExpression rhs) {
    return wrap(lhs.asIntegerExpression().mods(rhs));
  }

  @Override
  public IntegerStateExpression zero()  {
    return wrap(getExpressionManager().zero());
  }

  @Override
  public IntegerStateExpression ofBoolean(BooleanExpression b) {
    return wrap(b.ifThenElse(one(), zero()));
  }

  @Override
  public StateProperty toBoolean(StateExpression expr) {
    return expr.eq(zero());
  }

  @Override
  public IntegerStateExpression ifThenElse(BooleanExpression b,
      StateExpression thenExpr,
      StateExpression elseExpr) {
    return wrap(b.ifThenElse(thenExpr, elseExpr));
  }

  @Override
  public IntegerStateExpression unknown() {
    throw new UnsupportedOperationException();
  }

  @Override
  public IntegerStateExpression ofExpression(Expression x) {
    Preconditions.checkArgument(x.isInteger());
    return wrap(x.asIntegerExpression());
  }

  @Override
  public StateExpression unknown(Type type) {
    throw new UnsupportedOperationException();
  }

	@Override
	public StateExpression uminus(StateExpression expr) {
    return wrap(expr.asIntegerExpression().negate());
	}

	@Override
	public StateExpression lshift(StateExpression lhs, StateExpression rhs) {
		return wrap(lhs.asIntegerExpression().times(
				constant(2).pow(rhs)));
	}

	@Override
	public StateExpression rshift(StateExpression lhs, StateExpression rhs) {
		return wrap(lhs.asIntegerExpression().divides(
				constant(2).pow(rhs)));
	}

	@Override
	public StateExpression rem(StateExpression lhs, StateExpression rhs) {
		return wrap(lhs.asIntegerExpression().minus(
				lhs.asIntegerExpression().mods(
						rhs.asIntegerExpression()).times(
								rhs.asIntegerExpression())));
	}

	@Override
	public StateExpression signedRem(StateExpression lhs, StateExpression rhs) {
		return rem(lhs, rhs);
	}

	@Override
	public StateExpression signedDivide(StateExpression lhs, StateExpression rhs) {
		return divide(lhs, rhs);
	}

	@Override
  public StateExpression ofInteger(StateExpression x, int size) {
		Preconditions.checkArgument(x.isInteger());
		/* FIXME: do not support conversion between types with different size */
    return wrap(x.asIntegerExpression());
  }
}
