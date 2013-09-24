package edu.nyu.cascade.ir.expr;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.c.preprocessor.AliasAnalysis;
import edu.nyu.cascade.c.preprocessor.TypeCastAnalysis;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
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
  
  /** Get the current state of memory model. It's used to create a back door to
   * get the memory state update with assume statement (for _allocated predicate)
   */
  ExpressionClosure getCurrentState();
  
  /** Clear current state of memory model to avoid side-effect.
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
   * Get initial state - memory state and auxiliary structure state
   */
  Expression initialState();

  /**
   * Get state type - memory state and auxiliary structure state
   */
  Type getStateType();
  
  /**
   * Get memory model type
   */
  Type getMemoryType();
  
  /**
   * Get a fresh state - memory state and auxiliary structure state
   */
  Expression freshState();
 
  /**
   * create a left variables with <code>name</code> and store it 
   * to the auxiliary structure to ensure that right variables and 
   * left variables won't overlap
   * @param name
   */
  Expression createLval(String name);

  Expression addressOf(Expression content);
  
  /**
   * create a expression with constant <code>value</code>, used for
   * tuple type expression especially.
   */
  Expression castConstant(int value, xtc.type.Type type);
  
  /**
   * type conversion with <code>src</code> expression to target
   * <code>type</code>
   */
  Expression castExpression(Expression state, Expression src, xtc.type.Type targetType);
  
  /**
   * set pointer alias map for partition memory model
   */
  void setAliasAnalyzer(AliasAnalysis analyzer);
  
  /**
   * set pointer alias map for partition memory model
   */
  void setTypeCastAnalyzer(TypeCastAnalysis analyzer);

  BooleanExpression valid_free(Expression state, Expression ptr);

  BooleanExpression valid_malloc(Expression state, Expression ptr, Expression size);
}
