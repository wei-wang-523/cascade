package edu.nyu.cascade.fds;

import edu.nyu.cascade.prover.Expression;

public interface StateExpression extends Expression {
  public static interface Factory {
    StateExpression valueOf( Expression expr );
  }

  @Override
  StateProperty asBooleanExpression();
  
  StateProperty asStateProperty();
  
  @Override
  StateVariable asVariable();
  
  @Override
  IntegerStateExpression asIntegerExpression();
  
  @Override
  StateProperty eq(Expression e) ;

/*  StateProperty geq(Expression e) ;

  StateProperty gt(StateExpression e) ;

  StateProperty leq(StateExpression e) ;

  StateProperty lt(StateExpression e) ;
*/
  @Override
  StateProperty neq(Expression e) ;

  StateExpression prime() ;

  Expression toExpression();

  StateExpression unprime();

//  StateProperty iff(StateExpression e);
}
