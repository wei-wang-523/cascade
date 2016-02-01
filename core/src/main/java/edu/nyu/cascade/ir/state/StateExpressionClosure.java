package edu.nyu.cascade.ir.state;


import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;

public interface StateExpressionClosure {
  ExpressionManager getExpressionManager();
  /**
   * To evaluate current expression based on <code>state</code>,
   * this operation might cause side-effect on <code>state</code>
   * @param state
   * @return
   */
  Expression eval(StateExpression state);
  Type getOutputType();
	Expression getOutput();
}
