package edu.nyu.cascade.fds;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.type.IntegerType;

public interface IntegerStateExpression extends StateExpression,
    IntegerExpression {
  @Override
  StateProperty greaterThan(Expression e);
  @Override
  StateProperty greaterThanOrEqual(Expression e);
  @Override
  StateProperty lessThan(Expression e);
  @Override
  StateProperty lessThanOrEqual(Expression e);
  @Override
  IntegerStateExpression plus(Expression e) ;
  @Override
  IntegerStateExpression minus(Expression e) ;
  @Override  
  IntegerStateExpression negate();
  @Override
  IntegerStateExpression times(Expression e) ;
  @Override
  IntegerType getType();
}
