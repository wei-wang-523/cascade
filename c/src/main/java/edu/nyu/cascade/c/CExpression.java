package edu.nyu.cascade.c;

import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.c.CPrinter;
import edu.nyu.cascade.ir.impl.IRExpressionImpl;
import edu.nyu.cascade.util.IOUtils;

class CExpression extends IRExpressionImpl {
/*  public CExpression(Node sourceNode) {
    super(sourceNode);
  }*/

  public CExpression(Node sourceNode, Scope scope) {
    super(sourceNode,scope);
  }

/*  public static CExpression create(Node sourceNode) {
    return new CExpression(sourceNode);
  }*/

  public static CExpression create(Node sourceNode,SymbolTable.Scope scope) {
    return new CExpression(sourceNode,scope);
  }

  @Override
  public void format(Printer printer) {
    CPrinter cp = new CPrinter(printer);
    cp.dispatch(getSourceNode());
  }

  @Override
  public String toString() {
    return IOUtils.formatC(getSourceNode());
  }
}