package edu.nyu.cascade.ir.impl;

import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.type.Type;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRBooleanExpression;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRLocations;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.Pair;

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
  public Expression toBoolean(StateExpression pre, final ExpressionEncoder encoder) {
  	Expression testExprVal = testExpr.toExpression(pre, encoder);
  	Expression caseExprVal = caseLabel.toExpression(pre, encoder);
    Type testType = CType.getType(testExpr.getSourceNode());
    Type caseType = CType.getType(caseLabel.getSourceNode());
    
  	Pair<Expression, Expression> pair = encoder.getEncoding()
  			.arithTypeConversion(testExprVal, caseExprVal, testType, caseType);
    return pair.fst().eq(pair.snd());
  }

  @Override
  public Expression toExpression(StateExpression pre, ExpressionEncoder encoder) {
    throw new UnsupportedOperationException("CaseGuard.toExpression");
  }
  
  @Override
  public Expression toLval(StateExpression pre, ExpressionEncoder encoder) {
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
