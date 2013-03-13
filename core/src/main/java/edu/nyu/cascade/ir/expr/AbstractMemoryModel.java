package edu.nyu.cascade.ir.expr;

//import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;

public abstract class AbstractMemoryModel implements MemoryModel {
  private static final String DEFAULT_MEMORY_VARIABLE_NAME = "m";
  
  private final ExpressionEncoding encoding;
  
  protected AbstractMemoryModel(ExpressionEncoding encoding) {
    this.encoding = encoding;
  }
  
  @Override
  public Expression freshState() {
    return (Expression) getExpressionManager().variable(DEFAULT_MEMORY_VARIABLE_NAME,
        getStateType(), true);
    }

  @Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
    return ImmutableSet.of();
  }

  @Override
  public ExpressionEncoding getExpressionEncoding() {
    return encoding;
  }

  @Override
  public ExpressionManager getExpressionManager() {
    return encoding.getExpressionManager();
  }

  @Override
  public Expression initialState() {
    return freshState();
  }

  @Override
  public ExpressionClosure suspend(final Expression memoryVar, final Expression expr) {
    Preconditions.checkArgument(getStateType().equals(memoryVar.getType()) );

    return new ExpressionClosure() {
      @Override
      public Expression eval(Expression memory) {
        return expr
            .subst(ImmutableList.of(memoryVar), ImmutableList.of(memory));
      }

      @Override
      public Type getOutputType() {
        return expr.getType();
      }

      @Override
      public Type getInputType() {
        return memoryVar.getType();
      }

      @Override
      public ExpressionManager getExpressionManager() {
        return expr.getExpressionManager();
      }
    };
  }
}
