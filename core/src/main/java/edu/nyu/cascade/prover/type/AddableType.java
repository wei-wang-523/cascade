package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.RationalExpression;

public interface AddableType extends Type {
  RationalExpression zero() ;
  RationalExpression one() ;
  Expression add(Iterable<? extends Expression> addends) ;
  Expression add(Expression first, Expression... rest) ;
  Expression add(Expression a, Expression b) ;
  Expression subtract(Expression a, Expression b) ;
  Expression negate(Expression a) ;
}
