package edu.nyu.cascade.ir.expr;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public class LinearPointerEncoding <T extends Expression> extends AbstractTypeEncoding<T>
implements PointerEncoding<T> {
	
	private static final String UNKNOWN_VARIABLE_NAME = "ptr_encoding_unknown";
	
	private final IntegerEncoding<T> encoding;
	
  private LinearPointerEncoding(IntegerEncoding<T> _encoding) {
  	super(_encoding.getExpressionManager(), _encoding.getType());
  	encoding = _encoding;
	}
  
  public static <T extends Expression> LinearPointerEncoding<T> create(IntegerEncoding<T> _encoding) {
  	return new LinearPointerEncoding<T>(_encoding);
  }

	@Override
  public T ofExpression(Expression expr) {
	  return encoding.ofExpression(expr);
  }

	@Override
  public T ifThenElse(BooleanExpression b, T thenExpr, T elseExpr) {
	  return encoding.ifThenElse(b, thenExpr, elseExpr);
  }

	@Override
  public T incr(T expr) {
	  return encoding.incr(expr);
  }

	@Override
  public T decr(T expr) {
	  return encoding.decr(expr);
  }

	@SuppressWarnings("unchecked")
  @Override
  public T minus(T lhs, Expression rhs) {
	  return encoding.minus(lhs, (T) rhs);
  }

	@SuppressWarnings("unchecked")
  @Override
  public T plus(T first, Iterable<? extends Expression> rest) {
		ImmutableList.Builder<T> builder = new ImmutableList.Builder<T>();
		builder.add(first);
		for(Expression arg : rest) {
			builder.add((T) arg);
		}
	  return encoding.plus(builder.build());
  }

	@Override
  public T plus(T first, Expression... rest) {
	  return plus(first, Lists.newArrayList(rest));
  }

	@SuppressWarnings("unchecked")
  @Override
  public T plus(T first, Expression rest) {
	  return encoding.plus(first, (T) rest);
  }

	@Override
  public BooleanExpression toBoolean(T expr) {
	  return encoding.toBoolean(expr);
  }

	@Override
  public BooleanExpression neq(T lhs, T rhs) {
	  return encoding.neq(lhs, rhs);
  }

	@Override
  public BooleanExpression greaterThan(T lhs, T rhs) {
	  return encoding.greaterThan(lhs, rhs);
  }

	@Override
  public BooleanExpression greaterThanOrEqual(T lhs, T rhs) {
	  return encoding.greaterThanOrEqual(lhs, rhs);
  }

	@Override
  public BooleanExpression lessThan(T lhs, T rhs) {
	  return encoding.lessThan(lhs, rhs);
  }

	@Override
  public BooleanExpression lessThanOrEqual(T lhs, T rhs) {
	  return encoding.lessThanOrEqual(lhs, rhs);
  }

	@Override
  public T getNullPtr() {
		return encoding.zero();
  }

	@Override
  public T unknown() {
	  return encoding.variable(UNKNOWN_VARIABLE_NAME, true);
  }

	@Override
  public T freshPtr(String name, boolean fresh) {
	  return encoding.variable(name, fresh);
  }

	@Override
  public boolean isSyncEncoding() {
	  return false;
  }

	@Override
  public boolean isLinearEncoding() {
	  return true;
  }

	@Override
  public SyncPointerEncoding<? extends Expression, ? extends Expression> asSyncPointerEncoding() {
	  throw new UnsupportedOperationException();
  }

	@Override
  public LinearPointerEncoding<T> asLinearPointerEncoding() {
	  return this;
  }
}
