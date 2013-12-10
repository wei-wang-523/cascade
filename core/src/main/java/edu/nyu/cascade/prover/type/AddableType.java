package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.Expression;

public interface AddableType extends Type {
	Expression zero() ;
  Expression one() ;
  Expression add(Iterable<? extends Expression> addends) ;
  Expression add(Expression first, Expression... rest) ;
  Expression add(Expression a, Expression b) ;
  Expression subtract(Expression a, Expression b) ;
  Expression negate(Expression a) ;
}
