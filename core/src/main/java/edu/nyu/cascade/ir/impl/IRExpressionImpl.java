package edu.nyu.cascade.ir.impl;

import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRLocations;
import edu.nyu.cascade.ir.expr.ExpressionClosure;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;

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

  public void format(Printer printer) {
    printer.pln(toString());
  }
  
  public String toString() {
    return sourceNode.toString();
  }

  @Override
  public SymbolTable.Scope getScope() { return scope; }

  @Override
  public  ExpressionClosure toBoolean(ExpressionEncoder encoder) {
    return encoder.toBoolean(getSourceNode(),scope);
  }

  @Override
  public  ExpressionClosure toExpression(ExpressionEncoder encoder) {
    encoder.setScope(scope);
    return encoder.toInteger(getSourceNode(),scope);
  }

  @Override
  public  ExpressionClosure toLval(ExpressionEncoder encoder) {
    return encoder.toLval(getSourceNode(),scope);
  }
}
