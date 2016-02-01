package edu.nyu.cascade.ir.expr;

import java.util.List;

import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;

public class ExpressionClosures {
  public static ExpressionClosure eq(final ExpressionClosure arg1, final ExpressionClosure arg2) {
    Preconditions.checkArgument(arg1.getInputType().equals(arg2.getInputType()));
    Preconditions.checkArgument(arg1.getOutputType().equals(arg2.getOutputType()));

    return new ExpressionClosure() {
      @Override
      public Expression eval(Expression mem) {
//        Preconditions.checkArgument(mem.getType().equals( arg1.getInputType() ));
        return arg1.eval(mem).eq(arg2.eval(mem));
      }

      @Override
      public Type getOutputType() {
        return getExpressionManager().booleanType();
      }

      @Override
      public Type getInputType() {
        return arg1.getInputType();
      }

      @Override
      public ExpressionManager getExpressionManager() {
        return arg1.getExpressionManager();
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
