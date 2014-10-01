package edu.nyu.cascade.ir.impl;

import java.util.List;

import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.cascade.ir.IRBooleanExpression;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRLocations;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateExpressionClosure;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;

public class DefaultCaseGuard implements IRBooleanExpression {
  private final Node node;
  private final ImmutableList<CaseGuard> guards;
  private final IRLocation location;
  
  public DefaultCaseGuard(Node node, Iterable<CaseGuard> list) {
    Preconditions.checkArgument(!Iterables.isEmpty(list));
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
  public StateExpressionClosure toBoolean(final ExpressionEncoder encoder) {
    return new StateExpressionClosure() {
      @Override
      public Expression eval(StateExpression mem) {
        List<BooleanExpression> argExprs = Lists.newArrayList();
        ExpressionManager exprManager = null;
        for( CaseGuard guard : guards ) {
        	StateExpressionClosure closure = guard.toBoolean(encoder);
          Expression expr = closure.eval(mem);
          assert( expr.isBoolean() );
          argExprs.add(expr.asBooleanExpression());
          exprManager = expr.getExpressionManager();
        }
        return exprManager.or(argExprs).not();
      }

      @Override
      public Type getOutputType() {
        return encoder.getEncoding().getExpressionManager().booleanType();
      }
      
      @Override
      public ExpressionManager getExpressionManager() {
        return encoder.getEncoding().getExpressionManager();
      }

			@Override
      public Expression getOutput() {
				throw new UnsupportedOperationException();
      }
    };
  }

  @Override
  public StateExpressionClosure toExpression(ExpressionEncoder encoder){
    throw new UnsupportedOperationException("DefaultCaseGuard.toExpression");
  }

  @Override
  public StateExpressionClosure toLval(ExpressionEncoder encoder) {
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
