package edu.nyu.cascade.ir.state;

import java.util.Collection;

import xtc.tree.Node;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public interface StateFactory<T> {

	StateExpression resolvePhiNode(Collection<StateExpression> preStates);

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
	
	IRDataFormatter getDataFormatter();

	ExpressionEncoding getExpressionEncoding();
	
	/**
	 * Substitute the element state variable in <code>cleanState</code> with <code>stateArg</code>
	 * @param cleanState
	 * @param stateArg
	 * @return
	 */
	void propagateState(StateExpression cleanState, StateExpression stateArg);
	
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
   * @param info
   */
	void addStackVar(StateExpression state, Expression lval, IRVarInfo info);
	
  /**
   * Add the newly-declared stack array variable expression <code>lval</code> to 
   * <code>state</code> with variable size <code>rval</code>. If <code>state</code> 
   * is a multiple state or multiple lambda state, and doesn't contain the element 
   * state for <code>lval</code>, a new element state will be added into <code>state
   * </code>, and thus will cause side-effect
   * 
   * @param state
   * @param lval
	 * @param rval
   * @param info
   * @param sourceNode 
   */
	void addStackVarArray(StateExpression state, Expression lval, Expression rval, IRVarInfo info, Node sourceNode);

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
	 * Refresh the local variables and newly allocated regions
	 * @param state
	 * @param vars
	 * @param freshVars
	 * @return
	 */
	void substitute(StateExpression state, 
			Collection<? extends Expression> vars, Collection<? extends Expression> freshVars);
	
	void reset();

	/**
	 * Look up the size of variable length array <code>ptr</code> with source
	 * node <code>node</code>
	 * @param state
	 * @param ptr
	 * @param node
	 * @return
	 */
	Expression lookupSize(StateExpression state, Expression ptr, Node node);
	
	void setValidAccess(StateExpression preState, Expression lhsExpr, Node lNode);
	
	void setValidFree(StateExpression preState, Expression regionExpr, Node ptrNode);
	
	BooleanExpression stateToBoolean(StateExpression state);
	
	Collection<BooleanExpression> getAssumptions();
}
