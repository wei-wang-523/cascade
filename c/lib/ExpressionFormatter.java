package edu.nyu.cascade;

import java.math.BigInteger;

import xtc.Constants;
import xtc.tree.Attribute;
import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.tree.Visitor;
import xtc.type.Type;
import xtc.util.SymbolTable;
import edu.nyu.cascade.prover.IBooleanExpression;
import edu.nyu.cascade.prover.IExpression;
import edu.nyu.cascade.prover.IExpressionFactory;
import edu.nyu.cascade.prover.IExpressionManager;
import edu.nyu.cascade.prover.IIntegerExpression;
import edu.nyu.cascade.util.IOUtils;

public class ExpressionFormatter extends Visitor {
//  private final SymbolTable symbolTable;
  private final StringBuilder stringBuilder;
  private int recursionDepth;
  
  public ExpressionFormatter(SymbolTable symbolTable) {
//    this.symbolTable = symbolTable;
    this.stringBuilder = new StringBuilder();
    this.recursionDepth = 0;
  }

  public static String formatExpression(SymbolTable symbolTable, Node ast) {
    return (String) new ExpressionFormatter(symbolTable).dispatch(ast);
  }

  public String getExpression(Node ast) {
    return (String) dispatch(ast);
  }

  private void recurse(Object node) {
    recursionDepth++;
    dispatch((Node)node);
    recursionDepth--;
  }
  
  private String doReturn() {
    return recursionDepth > 0 ? null : stringBuilder.toString();
  }
  
  @Override
  public String unableToVisit(Node node) {
    return "<<unimplemented>>";
  }

  public String visitEqualityExpression(GNode node) {
    recurse(node.get(0));
    stringBuilder.append(node.getString(1));
    recurse(node.get(2));
    return doReturn();
  }

  public String visitLogicalAndExpression(GNode node) {
    recurse(node.get(0));
    stringBuilder.append(" && ");
    recurse(node.get(1));
    return doReturn();
  }

  public String visitPrimaryIdentifier(GNode node) {
    stringBuilder.append(node.getString(0));
    return doReturn();
  }
  
  public String visitCharacterConstant(GNode node) {
    return visitIntegerConstant(node);
  }
  
  public String visitIntegerConstant(GNode node) {
    Type intType = (Type) node.getProperty(Constants.TYPE);
    stringBuilder.append( intType.getConstant().toString() );
    return doReturn();
  }
  
  public String visitStringConstant(GNode node) {
    stringBuilder.append(node.getString(0));
    return doReturn();
  }
  
  public IExpression visitSubscriptExpression(GNode node) {
    // TODO: correct
    IOUtils.err()
        .println("APPROX: Treating index expression " + node + " as integer 0");
    return exprManager.zero();
    
  }

  public IBooleanExpression visitRelationalExpression(GNode node) {
    IIntegerExpression left = integerExpression((Node)node.get(0));
    String relOp = node.getString(1);
    IIntegerExpression right = integerExpression((Node) node.get(2));

    if (">".equals(relOp)) {
      return exprManager.gtExpression(left, right);
    } else if (">=".equals(relOp)) {
      return exprManager.gteExpression(left, right);
    } if ("<".equals(relOp)) {
      return exprManager.ltExpression(left, right);
    } else if ("<=".equals(relOp)) {
      return exprManager.lteExpression(left, right);
    } else {
      assert false;
      return null;
    }
  }

  private IIntegerExpression integerExpression(Node node) {
    return (IIntegerExpression) dispatch(node);
  }

  public IIntegerExpression visitAdditiveExpression(GNode node) {
    Node lhsNode = node.getNode(0);
    String additiveOperator = node.getString(1);
    Node rhsNode = node.getNode(2);

    IIntegerExpression lhsExpr = (IIntegerExpression) dispatch(lhsNode);
    IIntegerExpression rhsExpr = (IIntegerExpression) dispatch(rhsNode);

    if ("+".equals(additiveOperator)) {
      return exprManager.plusExpr(lhsExpr, rhsExpr);
    } else if ("-".equals(additiveOperator)) {
      return exprManager.minusExpr(lhsExpr, rhsExpr);
    } else {
      assert false;
      return null;
    }
  }
}
