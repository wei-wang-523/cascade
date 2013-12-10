package edu.nyu.cascade.prover.type;

import com.google.common.collect.ImmutableList;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.VariableExpression;

public interface FunctionType extends Type {
  Expression apply(Expression arg1, Expression... rest) ;

  Expression apply(Iterable<? extends Expression> args) ;

  Type getArgTypeAtIndex(int index);

  ImmutableList<? extends Type> getArgTypes();

  int getArity();

  Type getRangeType();
  
  String getName();
  
  VariableExpression variable(String name, boolean fresh) ;
}
