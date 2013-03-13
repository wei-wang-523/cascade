package edu.nyu.cascade.ir.expr;


public interface DualExpression<Int, Bool> {
//  IExpression<IBooleanType> toBooleanExpression();
  Int castToInteger() throws ExpressionFactoryException;
  Bool castToBoolean() throws ExpressionFactoryException;
}
