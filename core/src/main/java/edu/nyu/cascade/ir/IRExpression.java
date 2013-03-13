package edu.nyu.cascade.ir;

import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.ir.expr.ExpressionClosure;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;

public interface IRExpression {
  void format(Printer printer);

  Node getSourceNode();

  IRLocation getLocation();

  ExpressionClosure toBoolean(ExpressionEncoder encoder);

  ExpressionClosure toExpression(ExpressionEncoder encoder);

  ExpressionClosure toLval(ExpressionEncoder encoder);

  Scope getScope();
}
