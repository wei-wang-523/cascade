package edu.nyu.cascade.c;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.ir.expr.ExpressionClosure;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;

public class IncrementExpression extends CExpression {
  public static IncrementExpression create(CExpression op) {
    return new IncrementExpression(op);
  }
  
  private IncrementExpression(CExpression op) {
    super(op.getSourceNode(), op.getScope());
  }

  @Override
  public  ExpressionClosure toExpression(
      final ExpressionEncoder interp) {
    return new ExpressionClosure() {
      @Override
      public Expression eval(Expression mem) {
        Preconditions.checkArgument(mem.getType().equals( interp.getMemoryModel().getStateType() ));
        
        return interp.getEncoding().incr(
            IncrementExpression.super.toExpression(interp).eval(mem));
      }

      @Override
      public Type getOutputType() {
        return interp.getEncoding().getIntegerEncoding().getType();
      }

      @Override
      public Type getInputType() {
        return interp.getMemoryModel().getStateType();
      }

      @Override
      public ExpressionManager getExpressionManager() {
        return interp.getExpressionManager();
      }
    };
  }

  @Override
  public String toString() {
    return super.toString() + " + 1";
  }
}
