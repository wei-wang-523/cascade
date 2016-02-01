package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.List;

import xtc.tree.Node;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public interface StateFactory<T> {

	StateExpression resolvePhiNode(Collection<StateExpression> preStates);
	
	Expression cleanup(StateExpression state, Expression ptr);

	/**
	 * <code>ptr = malloc(...)</code>, <code>region</code> is the expression 
	 * assigned to <code>ptr</code>, <code>ptrNode</code> is the source node
	 * of <code>ptr</code>
	 */
	BooleanExpression applyValidMalloc(StateExpression state, Expression region, 
			Expression size, Node ptrNode);
	
	BooleanExpression applyMemoryTrack(StateExpression state);
	
	/**
	 * Initialize the <code>region</code> of memory with <code>size</code> 
	 * to be <code>value</code>
	 */
	BooleanExpression applyMemset(StateExpression state, Expression region, 
			Expression size, Expression value, Node ptrNode);
	
	/**
	 * Initialize the <code>region</code> of memory with <code>size</code> 
	 * to be <code>value</code>
	 */
	BooleanExpression applyMemcpy(StateExpression state, Expression destRegion, 
			Expression srcRegion, Expression size, Node destNode, Node srcNode);
	
	/**
	 * <code>free(region)</code>, <code>ptrNode</code> is the source node of 
	 * <code>ptr</code>
	 */
	BooleanExpression applyValidFree(StateExpression state, Expression region, 
			Node ptrNode);

	BooleanExpression validAccess(StateExpression state, Expression ptr, 
			Node ptrNode);

	BooleanExpression validAccessRange(StateExpression state, Expression ptr,
      Expression size, Node ptrNode);

	BooleanExpression getDisjointAssumption(StateExpression state);
	
	IRDataFormatter getDataFormatter();

	ExpressionEncoding getExpressionEncoding();
	
	/**
	 * Substitute <code>stateVar</code> in <code>cleanState</code> with <code>stateArg</code>
	 * @param cleanState
	 * @param stateVar
	 * @param stateArg
	 * @return
	 */
	void propagateState(StateExpression cleanState, StateExpression stateVar, StateExpression stateArg);
	
	/**
	 * Allocate a region at <code>ptr</code> with <code>size</code>
	 * @param state
	 * @param ptr
	 * @param size
	 * @param ptrNode
	 */
	void malloc(StateExpression state, Expression ptr, Expression size, Node ptrNode);
	
	/**
	 * Allocate a region at <code>ptr</code> with <code>size</code> and initialize the
	 * region to be zero
	 * @param state
	 * @param ptr
	 * @param size
	 * @param ptrNode
	 */
	void calloc(StateExpression state, Expression ptr, Expression nitem, Expression size, Node ptrNode);
	
	/**
	 * Allocate a region in stack at <code>ptr</code> with <code>size</code>
	 * @param state
	 * @param ptr
	 * @param size
	 * @param ptrNode
	 */
	void alloca(StateExpression state, Expression ptr, Expression size, Node ptrNode);

	/**
	 * Update the memory element of <code>state</code>
	 * @param state
	 * @param memIdx
	 * @param idxNode
	 * @param memVal
	 * @param valNode 
	 */
	void assign(StateExpression state, Expression memIdx, Node idxNode, Expression memVal, Node valNode);
	
	/**
	 * Initialize the static variable as default value, for static variables
	 * 
	 * @param currState
	 * @param lval
	 * @param lNode
	 */
	void initializeDefault(StateExpression currState, Expression lval, Node lNode);
	
	/**
	 * Initialize the variable with values
	 * 
	 * @param currState
	 * @param lval
	 * @param lNode
	 * @param rvals
	 * @param rNodes
	 */
	void initializeValues(StateExpression currState, Expression lval, Node lNode, 
			List<Expression> rvals, List<Node> rNodes);

	/**
	 * Update the size element of <code>state</code>
	 * @param state
	 * @param ptr
	 * @param ptrNode
	 */
	void free(StateExpression state, Expression ptr, Node ptrNode);
	
	/**
	 * Deference the content with in <code>state</code> of <code>index</code>
	 * @param state
	 * @param lvalNode
	 * @param lvalNode 
	 */
	Expression deref(StateExpression state, Expression index, Node idxNode);

	/**
	 * Create a fresh (empty) state
	 * @return
	 */
	StateExpression freshState();

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
	void addStackVar(StateExpression state, Expression lval, IRVarInfo info);

	<X> void setLabelAnalyzer(PreProcessor<X> preprocessor);
	
	
  /**
   * Create a clone of itself to keep clean of side-effect caused by 
   * following operations. Used in the <code>SimplePathEncoding</code> to 
   * analyze statements. Otherwise, the side-effect caused of the expression 
   * evaluation will change the
   * input state, which might also be the input state of other statements
   *  (e.g. in ite-branch), the side-effect of the if-branch 
   * statements will affect the analysis of else-branch statements
   * @param state
   * @return
   */
	StateExpression copy(StateExpression state);

	/**
	 * Get the corresponding state variable for <code>state</code>. If it is
	 * single, return the empty state (m_flat, size_flat). Otherwise, collect 
	 * the corresponding variable for the every sub-state of <code>state</code>
	 * 
	 * @param state
	 * @return
	 */
	StateExpression getStateVar(StateExpression state);

	StateExpressionClosure suspend(StateExpression stateVar, Expression expr);
	
	void reset();
}
