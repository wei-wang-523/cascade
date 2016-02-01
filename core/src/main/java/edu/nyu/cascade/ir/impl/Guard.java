package edu.nyu.cascade.ir.impl;

import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.ir.IRBooleanExpression;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.state.StateExpressionClosure;

public class Guard implements IRBooleanExpression {
  public static Guard create(IRExpression test) {
    return new Guard(test);
  }

/*  public static Guard create(Node test) {
    return new Guard(IRExpressionImpl.create(test));
  }*/

  private final IRExpression expression;
//  private final Node sourceNode;
  private final boolean negated;
//  private final IRLocation location;

  Guard(IRExpression expression) {
    this(expression, false);
  }

  Guard(IRExpression expression, boolean negated) {
//    this.sourceNode = expression;
    this.expression = expression;
    this.negated = negated;
//    location = IRLocations.ofNode(sourceNode);
  }

  @Override
  public void format(Printer printer) {
    printer.pln(toString());
  }

  public IRExpression getExpression() {
    return expression;
  }

  @Override
  public IRLocation getLocation() {
    return expression.getLocation();
    //    return location;
  }

  @Override
  public Node getSourceNode() {
    return expression.getSourceNode();
//    return sourceNode;
  }

  @Override
  public boolean isNegated() {
    return negated;
  }

  @Override
  public Guard negate() {
    return new Guard(getExpression(), !negated);
  }

  @Override
  public StateExpressionClosure toBoolean(ExpressionEncoder encoder) {
    return encoder.toBoolean(getSourceNode(), isNegated(), getScope());
  }

  @Override
  public StateExpressionClosure toExpression(ExpressionEncoder encoder) {
    throw new UnsupportedOperationException("Guard.toExpression");
  }

  @Override
  public StateExpressionClosure toLval(ExpressionEncoder encoder) {
    throw new UnsupportedOperationException("Guard.toLval");
  }

  @Override
  public String toString() {
    return (negated ? "!(" + expression + ")" : expression.toString());
  }

  @Override
  public Scope getScope() {
    return expression.getScope();
  }
}
