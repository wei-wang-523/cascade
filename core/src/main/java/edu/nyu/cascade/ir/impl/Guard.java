package edu.nyu.cascade.ir.impl;

import com.google.common.base.Preconditions;

import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.ir.IRBooleanExpression;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.prover.Expression;

public class Guard implements IRBooleanExpression {
  public static Guard create(IRExpression test) {
    return new Guard(test);
  }

  private final IRExpression expression;
  private final boolean negated;

  Guard(IRExpression expression) {
    this(expression, false);
  }

  Guard(IRExpression expression, boolean negated) {
  	Preconditions.checkNotNull(expression);
    this.expression = expression;
    this.negated = negated;
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
  public Expression toBoolean(StateExpression pre, ExpressionEncoder encoder) {
    return encoder.toBoolean(pre, getSourceNode(), isNegated(), getScope());
  }

  @Override
  public Expression toExpression(StateExpression pre, ExpressionEncoder encoder) {
    throw new UnsupportedOperationException("Guard.toExpression");
  }

  @Override
  public Expression toLval(StateExpression pre, ExpressionEncoder encoder) {
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
