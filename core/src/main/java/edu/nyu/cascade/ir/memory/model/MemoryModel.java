package edu.nyu.cascade.ir.memory.model;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateExpressionClosure;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;

public interface MemoryModel<T> {
  
  /**
   * Returns a boolean expression representing the proposition that the 
   * memory location identified by <code>ptr</code> is a valid pointer within an
   * allocated block of storage.
   */
  BooleanExpression validAccess(StateExpression state, Expression ptr);
  BooleanExpression validAccessRange(StateExpression state, Expression ptr, Expression size);
  
  /**
   * Returns a new program state, representing the assignment of the value
   * <code>rval</code> to the memory location <code>lval</code> in pre-state
   * <code>state</code>.
   */
  StateExpression assign(StateExpression state, Expression lval, Expression rval);
  
  /**
   * Returns an expression representing the value stored at the memory
   * location identified by expression <code>p</code>.
   */
  Expression deref(StateExpression state, Expression p) ;
  
  /** Create a closure for expression <code>expr</code> given the memory variable
   * <code>memory</code> wrt which it is defined.
   */
  StateExpressionClosure suspend(StateExpression state, Expression expr);
  
  /**
   * Allocate a region with size <code>size</code> to the memory location 
   * <code>ptr</code> in pre-state <code>state</code>.
   */
  StateExpression alloc(StateExpression state, Expression ptr, Expression size);
  
  /**
   * Free a region in memory at the memory location <code>ptr</code> in pre-state 
   * <code>state</code>.
   */
  StateExpression free(StateExpression state, Expression ptr);
  
  /**
   * Update <code>lval</code> in pre-state as unknown in pre-state <code>state</code>.
   */
  StateExpression havoc(StateExpression state, Expression lval);
  
  /**
   * Declare <code>lval</code> in pre-state <code>state</code>.
   */
  StateExpression declare(StateExpression state, Expression lval, IRVarInfo info);

  /**
   * Get expression encoding.
   */
  ExpressionEncoding getExpressionEncoding();

  /**
   * Get expression manager.
   */
  ExpressionManager getExpressionManager();
 
  /**
   * create a left variables with <code>name</code> and store it 
   * to the auxiliary structure to ensure that right variables and 
   * left variables won't overlap
   * @param name
   */
	Expression createLval(String name);
  
  /**
   * set pointer alias analyzer for partition memory model
   * set type analyzer for burstall memory model
   */
  <X> void setPreProcessor(PreProcessor<X> analyzer);

  /**
   * valid free operation
   */
  BooleanExpression validFree(StateExpression state, Expression ptr);

  /**
   * valid malloc operation
   */
  BooleanExpression validMalloc(StateExpression state, Expression ptr, Expression size);
	
	/**
	 * Get the state expression factory
	 * @return
	 */
	StateFactory<T> getStateFactory();
	
	/**
	 * Get the data formatter
	 * @return
	 */
	IRDataFormatter getDataFormatter();
}
