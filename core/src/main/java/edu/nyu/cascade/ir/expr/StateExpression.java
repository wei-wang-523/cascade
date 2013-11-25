package edu.nyu.cascade.ir.expr;

import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.prover.Expression;

public interface StateExpression extends Expression {
  public static interface Factory {
    StateExpression valueOf( Expression expr );
  }

  void setScope(Scope scope);
  
  Scope getScope();

  Expression toExpression();
}
