package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public class UnimplementedPointerEncoding<T extends Expression> implements PointerEncoding<T> {

	@Override
  public Type getType() {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public Expression symbolicConstant(String name, boolean fresh) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public VariableExpression toVariable(T x) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public T variable(String name, boolean fresh) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public ExpressionManager getExpressionManager() {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public boolean isEncodingFor(Expression x) {
	  // TODO Auto-generated method stub
	  return false;
  }

	@Override
  public T ofExpression(Expression expr) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public T ifThenElse(BooleanExpression b, T thenExpr, T elseExpr) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public T incr(T expr) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public T decr(T expr) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public T minus(T lhs, Expression rhs) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public T plus(T first, Iterable<? extends Expression> rest) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public T plus(T first, Expression... rest) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public T plus(T first, Expression rest) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public BooleanExpression toBoolean(T expr) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public BooleanExpression neq(T lhs, T rhs) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public BooleanExpression eq(T lhs, T rhs) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public BooleanExpression greaterThan(T lhs, T rhs) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public BooleanExpression greaterThanOrEqual(T lhs, T rhs) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public BooleanExpression lessThan(T lhs, T rhs) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public BooleanExpression lessThanOrEqual(T lhs, T rhs) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public T getNullPtr() {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public T unknown() {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public T freshPtr(String name, boolean fresh) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public TypeEncoding<?> getBaseEncoding() {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public IntegerEncoding<?> getOffsetEncoding() {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public boolean isBooleanEncoding() {
	  // TODO Auto-generated method stub
	  return false;
  }

	@Override
  public BooleanEncoding<? extends Expression> asBooleanEncoding() {
		throw new UnsupportedOperationException();
  }

	@Override
  public boolean isIntegerEncoding() {
	  // TODO Auto-generated method stub
	  return false;
  }

	@Override
  public IntegerEncoding<? extends Expression> asIntegerEncoding() {
		throw new UnsupportedOperationException();
  }

	@Override
  public boolean isPointerEncoding() {
	  // TODO Auto-generated method stub
	  return false;
  }

	@Override
  public PointerEncoding<? extends Expression> asPointerEncoding() {
		return this;
  }

}
