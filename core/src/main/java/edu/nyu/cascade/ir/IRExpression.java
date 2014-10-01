package edu.nyu.cascade.ir;

import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.state.StateExpressionClosure;

public interface IRExpression {
  void format(Printer printer);

  Node getSourceNode();

  IRLocation getLocation();

  StateExpressionClosure toBoolean(ExpressionEncoder encoder);

  StateExpressionClosure toExpression(ExpressionEncoder encoder);

  StateExpressionClosure toLval(ExpressionEncoder encoder);

  Scope getScope();
}
