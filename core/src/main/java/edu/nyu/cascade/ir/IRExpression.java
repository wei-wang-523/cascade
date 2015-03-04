package edu.nyu.cascade.ir;

import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.prover.Expression;

public interface IRExpression {
  void format(Printer printer);

  Node getSourceNode();

  IRLocation getLocation();

  Expression toBoolean(StateExpression pre, ExpressionEncoder encoder);

  Expression toExpression(StateExpression pre, ExpressionEncoder encoder);

  Expression toLval(StateExpression pre, ExpressionEncoder encoder);

  Scope getScope();
}
