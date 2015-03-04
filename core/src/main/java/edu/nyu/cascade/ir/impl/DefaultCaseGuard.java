package edu.nyu.cascade.ir.impl;

import java.util.List;

import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;

import edu.nyu.cascade.ir.IRBooleanExpression;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRLocations;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public class DefaultCaseGuard implements IRBooleanExpression {
  private final Node node;
  private final ImmutableList<CaseGuard> guards;
  private final IRLocation location;
  
  public DefaultCaseGuard(Node node, Iterable<CaseGuard> list) {
//    Preconditions.checkArgument(!Iterables.isEmpty(list));
    this.node = node;
    this.guards = ImmutableList.copyOf(list);
    location = IRLocations.ofNode(node);
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
    return node;
  }
  
  @Override
  public boolean isNegated() { return false; }

  @Override
  public IRBooleanExpression negate() {
    throw new UnsupportedOperationException("CaseGuard.negate");
  }

  @Override
  public Expression toBoolean(StateExpression pre, final ExpressionEncoder encoder) {
    List<BooleanExpression> argExprs = Lists.newArrayList();
    ExpressionEncoding exprEncoding = encoder.getEncoding();
    for( CaseGuard guard : guards ) {
    	Expression expr = guard.toBoolean(pre, encoder);
      assert( expr.isBoolean() );
      argExprs.add(expr.asBooleanExpression());
    }
    return exprEncoding.not(exprEncoding.or(argExprs));
  }

  @Override
  public Expression toExpression(StateExpression pre, ExpressionEncoder encoder){
    throw new UnsupportedOperationException("DefaultCaseGuard.toExpression");
  }

  @Override
  public Expression toLval(StateExpression pre, ExpressionEncoder encoder) {
    throw new UnsupportedOperationException("DefaultCaseGuard.toLval");
  }

  @Override
  public String toString() {
    return "!(" + Joiner.on(" || ").join(guards) + ")";
  }

  @Override
  public Scope getScope() {
    return guards.get(0).getScope();
  }

}
