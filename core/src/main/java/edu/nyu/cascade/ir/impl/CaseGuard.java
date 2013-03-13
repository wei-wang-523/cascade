package edu.nyu.cascade.ir.impl;

import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.ir.IRBooleanExpression;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRLocations;
import edu.nyu.cascade.ir.expr.ExpressionClosure;
import edu.nyu.cascade.ir.expr.ExpressionClosures;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;

public class CaseGuard implements IRBooleanExpression {
  private final IRExpression testExpr, caseLabel;
  private final Node sourceNode;
  private final IRLocation location;
  
  public CaseGuard(IRExpression testExpr, IRExpression caseLabel) {
    this.testExpr = testExpr;
    this.caseLabel = caseLabel;
    sourceNode = caseLabel.getSourceNode();
    location = IRLocations.ofNode(sourceNode);
  }

  @Override
  public void format(Printer printer) {
    printer.pln(toString());
  }
  
  @Override
  public IRLocation getLocation() {
    return location;
  }

  @Override
  public Node getSourceNode() {
    return sourceNode;
  }

  @Override
  public boolean isNegated() { return false; }

  @Override
  public IRBooleanExpression negate() {
    throw new UnsupportedOperationException("CaseGuard.negate");
  }

  @Override
  public  ExpressionClosure toBoolean(ExpressionEncoder encoder) {
    return ExpressionClosures.eq(testExpr.toExpression(encoder),caseLabel.toExpression(encoder));
  }

  @Override
  public  ExpressionClosure toExpression(ExpressionEncoder encoder) {
    throw new UnsupportedOperationException("CaseGuard.toExpression");
  }
  
  @Override
  public  ExpressionClosure toLval(ExpressionEncoder encoder) {
    throw new UnsupportedOperationException("CaseGuard.toLval");
  }

  @Override
  public String toString() {
    return testExpr.toString() + " == " + caseLabel.toString();
  }

  public Scope getScope() {
    return caseLabel.getScope();
  }

}
