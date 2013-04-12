package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

final class MemoryExpression {
  private final ExpressionManager exprManager;
  private final VariableExpression variable;
  private final ArrayExpression expr;

  public MemoryExpression(ExpressionManager exprManager, String name, Type type) {
    this.exprManager = exprManager;
    variable = exprManager.arrayVar(name, type, type, true);
    expr = variable.asArray();
  }
  
  private MemoryExpression(ExpressionManager exprManager,
      VariableExpression variable,
      ArrayExpression expr) {
    this.exprManager = exprManager;
    this.variable = variable;
    this.expr = expr;
  }
  
  Expression deref(Expression e) {
    Preconditions.checkArgument(expr.getIndexType().equals(e.getType()));
    return exprManager.index(expr, e);
  }
  
  VariableExpression getVariable() { return variable; }
  
  ArrayExpression toExpression() {
    return expr;
  }
  
  MemoryExpression update(Expression addr, Expression val) {
    Preconditions.checkArgument(expr.getIndexType().equals(addr.getType()));
    Preconditions.checkArgument(expr.getElementType().equals(val.getType()));
    return new MemoryExpression(exprManager, variable, expr.update(addr, val));
  }
}
