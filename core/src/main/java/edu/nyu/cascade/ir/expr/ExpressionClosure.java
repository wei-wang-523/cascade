package edu.nyu.cascade.ir.expr;


import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;

public interface ExpressionClosure {
/*  ExpressionEncoding<Expr> getEncoding();
  MemoryModel<Expr,Mem> getMemoryModel();
*/  
  ExpressionManager getExpressionManager();
  Expression eval(Expression mem);
  Type getOutputType();
  Type getInputType();
}
