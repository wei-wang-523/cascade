package edu.nyu.cascade.ir.expr.bak;

import xtc.tree.Node;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionClosure;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.Type;

public interface MemoryModel {
  
  /**
   * Returns a boolean expression representing the proposition that the 
   * memory location identified by <code>ptr</code> is a valid pointer within an
   * allocated block of storage.
   */
  BooleanExpression valid(Expression state, Expression ptr);
  BooleanExpression valid(Expression state, Expression ptr, Expression size);
  
  /**
   * Returns a new program state, representing the assignment of the value
   * <code>rval</code> to the memory location <code>lval</code> in pre-state
   * <code>state</code>.
   */
  Expression assign(Expression state, Expression lval, Expression rval);
  
  /**
   * Returns an expression representing the value stored at the memory
   * location identified by expression <code>p</code>.
   */
  Expression deref(Expression state, Expression p) ;
  
  /** Create a closure for expression <code>expr</code> given the memory variable
   * <code>memory</code> wrt which it is defined.
   */
  ExpressionClosure suspend(Expression state, Expression expr);
  
  /** Removed in updated version
   * Get the current state of memory model. It's used to create a back door to
   * get the memory state update with assume statement (for _allocated predicate)
   */
	ExpressionClosure getCurrentState();

  /** Removed in updated version
   * Clear current state of memory model to avoid side-effect.
   */
	void clearCurrentState();
  
  /**
   * Allocate a region with size <code>size</code> to the memory location 
   * <code>ptr</code> in pre-state <code>state</code>.
   */
  Expression alloc(Expression state, Expression ptr, Expression size);
  
  /**
   * Allocate a array or struct with size <code>size</code> to the memory location 
   * <code>ptr</code> in pre-state <code>state</code>.
   */
  Expression declareStruct(Expression state, Expression ptr, Expression size);
  
  /**
   * Allocate a array or struct with size <code>size</code> to the memory location 
   * <code>ptr</code> in pre-state <code>state</code>.
   */
  Expression declareArray(Expression state, Expression ptr, Expression size);
  
  /**
   * Free a region in memory at the memory location <code>ptr</code> in pre-state 
   * <code>state</code>.
   */
  Expression free(Expression state, Expression ptr);
  
  /**
   * Update <code>lval</code> in pre-state as unknown in pre-state <code>state</code>.
   */
  Expression havoc(Expression state, Expression lval);
  
  /**
   * Assume a region with size <code>size</code> to the memory location 
   * <code>ptr</code> is allocated in pre-state <code>state</code>.
   */
  BooleanExpression allocated(Expression state, Expression ptr, Expression size);
  
  /**
   * Get assumptions.
   * @param state
   * @return Set of assumptions.
   */
  ImmutableSet<? extends BooleanExpression> getAssumptions(Expression state);

  /**
   * Get expression encoding.
   */
  ExpressionEncoding getExpressionEncoding();

  /**
   * Get expression manager.
   */
  ExpressionManager getExpressionManager();

  /**
   * Get initial state - memory state and auxiliary structures state
   */
  Expression initialState();

  /**
   * Get state type - memory state and auxiliary structures state
   */
  Type getStateType();
  
  /**
   * Set state type, return if changed
   */
  boolean setStateType(Type stateType);
  /**
   * Get a fresh state - memory state and auxiliary structure state
   */
  Expression freshState();
 
  /**
   * create a left variables with <code>name</code> and store it 
   * to the auxiliary structure to ensure that right variables and 
   * left variables won't overlap
   * @param state
   * @param varInfo 
   * @param name
   * @param string 
   */
	Expression createLval(Expression state, String name, IRVarInfo varInfo, Node node);

  Expression addressOf(Expression content);
  
  /**
   * set pointer alias map for partition memory model
   */
  void setPreProcessor(PreProcessor<?> analyzer);

  /**
   * valid free operation
   */
  BooleanExpression valid_free(Expression state, Expression ptr);

  /**
   * valid malloc operation
   */
  BooleanExpression valid_malloc(Expression state, Expression ptr, Expression size);
  
  /**
   * Substitute the size array element in state type.
   */
  Expression substSizeArr(Expression expr);
	
  /**
   * Combine the previous record states with <code>guard</code>
   * @param guard
   * @param rec_1
   * @param rec_0
   * @return new record expression with only elements with same name
   */
	Expression combineRecordStates(BooleanExpression guard,
			RecordExpression rec_1, RecordExpression rec_0);
	
	/**
	 * Update <code>state</code> with new <code>elems</code>, 
	 * @param state
	 * @param elems
	 * @return an updated state
	 */
	TupleExpression getUpdatedState(Expression state, Expression... elems);
	TupleExpression getUpdatedState(Expression state, Iterable<Expression> elems);
}
