package edu.nyu.cascade.prover;

import com.google.common.collect.ImmutableList;

import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Type;

public interface FunctionExpression extends
    Expression {
  Expression apply(Expression first, Expression... rest) ;
  Expression apply(Iterable<? extends Expression> args) ;
  ImmutableList<? extends Type> getArgTypes(); 
  Type getRange();
  @Override
  FunctionType getType();
  String getName();
}
