package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.Expression;

public interface MultiplicativeType extends Type {
  Expression one() ;
  Expression mult(Iterable<? extends Expression> terms) ;
  Expression mult(Expression left, Expression right) ;
  Expression divide(Expression left, Expression right) ;
  Expression pow(Expression base, Expression exp) ;
}
