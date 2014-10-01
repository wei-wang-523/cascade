package edu.nyu.cascade.ir.state;

import java.util.Collection;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public interface StateFactory<T> {
  
  /**
   * Evaluate <code>expr</code> by replacing <code>stateVar</code>'s
   * (1). state elements (for normal expression)
   * (2). safety predicates (for validAccess(...) and validAccessRange(...))
   * with those in <code>state</code>
   * 
   * @param expr
   * @param stateVar
   * @param state
   * @return
   */
  Expression eval(Expression expr, StateExpression stateVar, StateExpression state);

	StateExpression resolvePhiNode(Collection<StateExpression> preStates);
	
	Expression cleanup(StateExpression state, Expression ptr);

	Expression applyValidMalloc(StateExpression state, Expression ptr, Expression size);
	
	BooleanExpression applyValidFree(StateExpression state, Expression ptr);

	Expression validAccess(StateExpression state, Expression arg);

	Expression validAccessRange(StateExpression state, Expression ptr,
      Expression size);

	Expression getDisjointAssumption(StateExpression state);
	
	IRDataFormatter getDataFormatter();

	ExpressionEncoding getExpressionEncoding();
	
	StateExpression propagateState(StateExpression cleanState, StateExpression stateVar, StateExpression stateArg);
	
	StateExpression alloc(StateExpression state, Expression ptr, Expression size);

	/**
	 * Update the memory element of <code>state</code>
	 * @param state
	 * @param memory
	 * @return updated state
	 */
	StateExpression updateMemState(StateExpression state, Expression memIdx,
      Expression memVal);

	/**
	 * Update the sizeArr element of <code>state</code>
	 * @param state
	 * @param sizeArr
	 * @return updated state
	 */
	StateExpression updateSizeState(StateExpression state, Expression sizeIdx,
      Expression sizeVal);
	
	/**
	 * Deference the content with in memory of <code>index</code>
	 */
	Expression deref(StateExpression state, Expression index);

	/**
	 * Create a fresh (empty) state
	 * @return
	 */
	StateExpression freshState();
	
	/**
	 * Clean the side-effect on the <code>fromState</code> on <code>toState</code>
	 * 
	 * In expression encoding, new labels may generated for function expression
	 * like validAccess(ptr), validAccessRange(ptr, size), fresh labels may created
	 * for ptr and size, and store them in the label table of <code>fromState</code>.
	 * 
	 * Here to propagate those fresh labels into <code>toState</code>, and substitute
	 * the memory var and size var in ptr and size expressions before store them
	 * into the label table of <code>toState</code>. 
	 */
	void propagateNewInfo(StateExpression fromState, StateExpression toState);

  /**
   * Add the newly-declared stack variable expression <code>lval</code> to 
   * <code>state</code>. If <code>state</code> is a multiple state or multiple
   * lambda state, and doesn't contain the element state for <code>lval</code>,
   * a new element state will be added into <code>state</code>, and thus will
   * cause side-effect
   * 
   * @param state
   * @param lval
   * @return the updated state
   */
	StateExpression addStackVar(StateExpression state, Expression lval, IRVarInfo info);

	<X> void setLabelAnalyzer(PreProcessor<X> preprocessor);

	StateExpression scopeOptimize(StateExpression preEntState,
			StateExpression retState);
}
