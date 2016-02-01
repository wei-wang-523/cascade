package edu.nyu.cascade.ir.state;


import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.Type;

public interface StateExpressionClosure {
  /**
   * To evaluate current expression based on <code>state</code>,
   * this operation might cause side-effect on <code>state</code>
   * @param state
   * @return
   */
  Expression eval(StateExpression state);
  StateExpression getStateVar();
  Type getExprType();
	Expression getExpression();
}
