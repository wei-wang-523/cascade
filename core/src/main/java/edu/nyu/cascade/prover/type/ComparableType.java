package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public interface ComparableType extends Type {
  BooleanExpression gt(Expression a, Expression b) ;
  BooleanExpression geq(Expression a, Expression b) ;
  BooleanExpression lt(Expression a, Expression b) ;
  BooleanExpression leq(Expression a, Expression b) ;
  BooleanExpression sgt(Expression a, Expression b) ;
  BooleanExpression sgeq(Expression a, Expression b) ;
  BooleanExpression slt(Expression a, Expression b) ;
  BooleanExpression sleq(Expression a, Expression b) ;
}
