package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.VariableExpression;

public interface VariableEncoding<T> {
  T ofVariableExpression(VariableExpression x);
  VariableExpression toVariableExpression(T x);
}
