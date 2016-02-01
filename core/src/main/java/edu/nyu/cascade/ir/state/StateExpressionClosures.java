package edu.nyu.cascade.ir.state;

import java.util.List;

import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.base.Preconditions;

import edu.nyu.cascade.ir.expr.ExpressionClosure;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;

public class StateExpressionClosures {
  public static StateExpressionClosure eq(final StateExpressionClosure arg1, final StateExpressionClosure arg2) {
  	/* FIXME: this checking doesn't fit for multi-state encoding */
//   Preconditions.checkArgument(EqualsUtil.areEqual(arg1.getInputTypes(), arg2.getInputTypes()));
    Preconditions.checkArgument(arg1.getOutputType().equals(arg2.getOutputType()));

    return new StateExpressionClosure() {
      @Override
      public Expression eval(StateExpression state) {
        return arg1.eval(state).eq(arg2.eval(state));
      }

      @Override
      public Type getOutputType() {
        return getExpressionManager().booleanType();
      }

      @Override
      public ExpressionManager getExpressionManager() {
        return arg1.getExpressionManager();
      }
      
      @Override
      public Expression getOutput() {
      	throw new UnsupportedOperationException();
      }
    };
  }

  public static ExpressionClosure nor(final Iterable<? extends ExpressionClosure> args) {
    Preconditions.checkArgument(!Iterables.isEmpty(args));
    
    return new ExpressionClosure() {
      @Override
      public Expression eval(Expression mem) {
        List<BooleanExpression> argExprs = Lists.newArrayList();
        ExpressionManager exprManager = null;
        for( ExpressionClosure arg : args ) {
          assert( arg.getInputType().equals( mem.getType() ));
          assert( arg.getOutputType().isBoolean() );
          
          BooleanExpression argExpr = arg.eval(mem).asBooleanExpression();
          argExprs.add(argExpr);
          if( exprManager != null ) {
            assert( exprManager.equals( argExpr.getExpressionManager() ));
          } else {
            exprManager = argExpr.getExpressionManager();
          }
        }
        assert( exprManager != null );
        return exprManager.or(argExprs).not();
      }

      @Override
      public Type getOutputType() {
        return getExpressionManager().booleanType();
      }

      @Override
      public Type getInputType() {
        return Iterables.get(args, 0).getInputType();
      }

      @Override
      public ExpressionManager getExpressionManager() {
        return Iterables.get(args,0).getExpressionManager();
      }
    };
    
  }
}
