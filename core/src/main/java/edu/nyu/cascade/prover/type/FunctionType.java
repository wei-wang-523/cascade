package edu.nyu.cascade.prover.type;

import com.google.common.collect.ImmutableList;

public interface FunctionType extends Type {
  Type getArgTypeAtIndex(int index);

  ImmutableList<? extends Type> getArgTypes();

  int getArity();

  Type getRangeType();
  
  String getName();
}
