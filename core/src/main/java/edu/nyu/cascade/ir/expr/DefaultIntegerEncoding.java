package edu.nyu.cascade.ir.expr;

import java.math.BigInteger;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.type.Type;

public class DefaultIntegerEncoding extends
    AbstractTypeEncoding<IntegerExpression> implements
    IntegerEncoding<IntegerExpression> {
  private static final String UNKNOWN_VARIABLE_NAME = "int_encoding_unknown";

  public DefaultIntegerEncoding(ExpressionManager exprManager) {
    super(exprManager, exprManager.integerType());
  }

  @Override
  public IntegerExpression bitwiseAnd(IntegerExpression a, IntegerExpression b) {
    return unknown();
  }
  
  @Override
  public IntegerExpression bitwiseNegate(IntegerExpression a) {
    return unknown();
  }
  
  @Override
  public IntegerExpression bitwiseOr(IntegerExpression a, IntegerExpression b) {
    return unknown();
  }
  
  @Override
  public IntegerExpression bitwiseXor(IntegerExpression a, IntegerExpression b) {
    return unknown();
  }

  @Override
  public IntegerExpression characterConstant(int c) {
  	return constant(c);
  }
  
  @Override
  public IntegerExpression constant(int c) {
    return getExpressionManager().constant(c);
  }
  
  @Override
  public IntegerExpression constant(long c) {
    return getExpressionManager().constant(c);
  }
  
  @Override
  public IntegerExpression constant(BigInteger c, long size) {
    return getExpressionManager().constant(c);
  }

  @Override
  public IntegerExpression decr(IntegerExpression expr) {
    return expr.minus(one());
  }

  @Override
  public BooleanExpression distinct(Iterable<? extends IntegerExpression> exprs) {
    return getExpressionManager().distinct(exprs);
  }

  @Override
  public BooleanExpression greaterThan(IntegerExpression lhs,
      IntegerExpression rhs) {
    return lhs.greaterThan(rhs);
  }
  

  @Override
  public BooleanExpression signedGreaterThan(IntegerExpression lhs,
      IntegerExpression rhs) {
    return greaterThan(lhs, rhs);
  }

  @Override
  public BooleanExpression greaterThanOrEqual(IntegerExpression lhs,
      IntegerExpression rhs) {
    return lhs.greaterThanOrEqual(rhs);
  }

  @Override
  public BooleanExpression signedGreaterThanOrEqual(IntegerExpression lhs,
      IntegerExpression rhs) {
    return greaterThanOrEqual(lhs, rhs);
  }

  @Override
  public IntegerExpression ifThenElse(BooleanExpression b,
      IntegerExpression thenExpr, IntegerExpression elseExpr) {
    return b.ifThenElse(thenExpr, elseExpr).asIntegerExpression();
  }

  @Override
  public IntegerExpression incr(IntegerExpression expr) {
    return expr.plus(one());
  }

  @Override
  public BooleanExpression lessThan(IntegerExpression lhs, IntegerExpression rhs) {
    return lhs.lessThan(rhs);
  }
  
  @Override
  public BooleanExpression signedLessThan(IntegerExpression lhs, IntegerExpression rhs) {
    return lessThan(lhs, rhs);
  }

  @Override
  public BooleanExpression lessThanOrEqual(IntegerExpression lhs,
      IntegerExpression rhs) {
    return lhs.lessThanOrEqual(rhs);
  }
  
  @Override
  public BooleanExpression signedLessThanOrEqual(IntegerExpression lhs, IntegerExpression rhs) {
    return lessThanOrEqual(lhs, rhs);
  }

  @Override
  public IntegerExpression minus(IntegerExpression lhs, IntegerExpression rhs) {
    return lhs.minus(rhs);
  }
  
  @Override
  public IntegerExpression times(IntegerExpression lhs, IntegerExpression rhs) {
    return lhs.times(rhs);
  }
  
  @Override
  public IntegerExpression divide(IntegerExpression lhs, IntegerExpression rhs) {
    return lhs.divides(rhs);
  }
  
  @Override
  public IntegerExpression mod(IntegerExpression lhs, IntegerExpression rhs) {
    return lhs.mods(rhs);
  }

  @Override
  public IntegerExpression negate(IntegerExpression arg) {
    return arg.negate();
  }

  @Override
  public BooleanExpression neq(IntegerExpression lhs, IntegerExpression rhs) {
    return lhs.neq(rhs);
  }

  @Override
  public IntegerExpression ofBoolean(BooleanExpression b) {
    return ifThenElse(b, one(), zero());
  }
  
  @Override
  public IntegerExpression ofInteger(IntegerExpression i, int size) {
  	/* FIXME: default integer encoding do not support casting between
  	 * different integer kind
  	 */
    return i;
  }
  
  @Override
  public IntegerExpression ofInteger(IntegerExpression i, int size, boolean isSigned) {
  	/* FIXME: default integer encoding do not support casting between
  	 * different integer kind
  	 */
    return i;
  }

  @Override
  public IntegerExpression ofExpression(Expression x) {
    Preconditions.checkArgument(x.isInteger());
    return x.asIntegerExpression();
  }

  @Override
  public IntegerExpression one() {
    return getExpressionManager().one();
  }

  @Override
  public IntegerExpression plus(IntegerExpression first, IntegerExpression... rest) {
    return first.plus(rest);
  }

  @Override
  public IntegerExpression plus(IntegerExpression lhs, IntegerExpression rhs) {
    return lhs.plus(rhs);
  }

  @Override
  public IntegerExpression plus(IntegerExpression first, Iterable<? extends IntegerExpression> rest) {
    return first.plus(rest);
  }

  @Override
  public BooleanExpression toBoolean(IntegerExpression expr) {
    return expr.neq(zero());
  }

  @Override
  public IntegerExpression unknown() {
    return getType().asInteger().variable(UNKNOWN_VARIABLE_NAME, true);
  }

  @Override
  public IntegerExpression zero() {
    return getExpressionManager().zero();
  }

  @Override
  public IntegerExpression unknown(long size) {
    return unknown();
  }

	@Override
	public IntegerExpression uminus(IntegerExpression expr) {
		return expr.negate();
	}
	
	@Override
	public IntegerExpression uplus(IntegerExpression expr) {
		return expr;
	}

	@Override
	public IntegerExpression lshift(IntegerExpression lhs, IntegerExpression rhs) {
		return lhs.times(constant(2).pow(rhs));
	}

	@Override
	public IntegerExpression rshift(IntegerExpression lhs, IntegerExpression rhs) {
		return ifThenElse(lhs.greaterThanOrEqual(zero()), lhs.divides(constant(2).pow(rhs)),
				uminus(lhs).divides(constant(2).pow(rhs)));
	}
	
	@Override
	public IntegerExpression signedRshift(IntegerExpression lhs, IntegerExpression rhs) {
		return lhs.divides(constant(2).pow(rhs));
	}

	@Override
	public IntegerExpression rem(IntegerExpression lhs, IntegerExpression rhs) {
		return lhs.minus(lhs.mods(rhs).times(rhs));
	}

	@Override
	public IntegerExpression signedRem(IntegerExpression lhs,
			IntegerExpression rhs) {
		return rem(lhs, rhs);
	}

	@Override
	public IntegerExpression signedDivide(IntegerExpression lhs,
			IntegerExpression rhs) {
		return divide(lhs, rhs);
	}

  @Override
  public IntegerExpression variable(String name, Type type, boolean fresh) {
  	Preconditions.checkArgument(type.isInteger());
  	return type.asInteger().variable(name, fresh);
  }
}
