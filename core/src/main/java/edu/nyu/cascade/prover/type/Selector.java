package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;

public interface Selector {
  Expression apply(Expression x);
  ExpressionManager getExpressionManager();
  String getName();
  Constructor getConstructor();
  Type getType();
  int getTypeRef();
}
