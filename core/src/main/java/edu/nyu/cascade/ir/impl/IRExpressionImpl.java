package edu.nyu.cascade.ir.impl;

import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRLocations;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.IOUtils;

public class IRExpressionImpl implements IRExpression {
/*  public static IRExpressionImpl create(Node sourceNode) {
    return new IRExpressionImpl(sourceNode);
  }*/

  public static IRExpressionImpl create(Node sourceNode,SymbolTable.Scope scope) {
    return new IRExpressionImpl(sourceNode,scope);
  }

  @Override
  public Node getSourceNode() {
    return sourceNode;
  }
  
  @Override
  public IRLocation getLocation() {
    return location;
  }

 /* protected IRExpressionImpl(Node sourceNode) {
    this(sourceNode,null);
  }*/

  protected IRExpressionImpl(Node sourceNode,SymbolTable.Scope scope) {
    this.sourceNode = sourceNode;
    this.scope = scope;
    location = IRLocations.ofNode(sourceNode);
  }

  private final Node sourceNode;
  private final SymbolTable.Scope scope;
  private final IRLocation location;

  @Override
  public void format(Printer printer) {
    printer.pln(toString());
  }
  
  @Override
  public String toString() {
    return IOUtils.formatC(sourceNode);
  }

  @Override
  public SymbolTable.Scope getScope() { return scope; }

  @Override
  public Expression toBoolean(StateExpression pre, ExpressionEncoder encoder) {
    return encoder.toBoolean(pre, getSourceNode(),scope);
  }

  @Override
  public  Expression toExpression(StateExpression pre, ExpressionEncoder encoder) {
    return encoder.toExpression(pre, getSourceNode(),scope);
  }

  @Override
  public  Expression toLval(StateExpression pre, ExpressionEncoder encoder) {
    return encoder.toLval(pre, getSourceNode(),scope);
  }
}
