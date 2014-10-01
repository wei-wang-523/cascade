package edu.nyu.cascade.ir;

import java.util.List;

import xtc.tree.Node;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.path.PathEncoding;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateExpressionClosure;

public interface IRStatement {
  /**
   * Enumeration of all allowed IR nodes.
   */
  public enum StatementType {
      
      // Basic statements
      
  	  /** Declare a symbol */
  		DECLARE,
      /** Assignment of values to a variable (set of variables) */ 
      ASSIGN,
      /** Allocate a region */
      ALLOC,
      /** Change the type of a by casting */
      CAST,
      /** Free a region in memory */
      FREE,
      /** Empty instruction node */
      SKIP,
      /** Call a procedure */
      CALL,
      /** Return from a procedure */
      RETURN,
      /** Declare enum type */
      ENUM,
      
      // Label statements
      
      /** Mark the start of statements lifted from loop for havoc */
      LIFT_BEGIN,
      /** Mark the end of statements lifted from loop for havoc */
      LIFT_END,
      /** Mark the enter into a scope */
      FUNC_ENT,
      /** Mark the exit out of a scope */
      FUNC_EXIT,
      
      // Multi-threads statements
      
      /** Send over a channel */
      SEND,
      /** Receive over a channel */
      RECEIVE,
      /** Request a semaphore */ 
      REQUEST_SEMAPHORE,
      /** Release a semaphore */ 
      RELEASE_SEMAPHORE,
      /** Fair waiting node */
      AWAIT,
      
      // Schematic statements
      
      /** Critical section node (abstraction of work that has to finish) */
      CRITICAL_SECTION,
      /** Non-Critical section node (abstraction of arbitrary work) */
      NON_CRITICAL_SECTION,
      /** Production activity node */
      PRODUCE,
      /** Consumption activity node */
      CONSUME,
      
      // Compound statements
      
      /** A fork node, starting a number of threads running in parallel */
      FORK_PARALLEL,
      /** A join node, for a given fork node, joins the treads to a single execution thread */
      JOIN_PARALLEL,
      
      // Cascade command
      
      /** An assertion, aborts if its argument is false */
      ASSERT,
      /** An assumption, used to represent guards on paths */
      ASSUME,
      /** Havoc, assign arbitrary value to the variable */
      HAVOC
  };
  
  void addPreLabel(String label);
  void addPreLabels(Iterable<String> labels);
  void addPostLabel(String label);
  void addPostLabels(Iterable<String> labels);

  Node getSourceNode();

  /**
   * Get the pre-condition guaranteeing the statement won't fail, using the
   * given expression factory. E.g., if the statement is
   * <code>assert x!=null</code>, then the pre-condition is <code>x!=null</code>.
   * @throws ExpressionFactoryException 
   */
  StateExpressionClosure getPreCondition(ExpressionEncoder  encoder);

  /**
   * Get the strongest post-condition of the statement, using the given
   * expression factory, given a pre-condition. E.g., if the statement is
   * <code>assert x!=null</code> and the pre-condition is <code>P</code>, then
   * the post-condition will be <code>P && x!=null</code>.
   * @throws ExpressionFactoryException 
   */
  StateExpression getPostCondition(PathEncoding factory, StateExpression preCondition);
  
  StatementType getType();
  ImmutableList<IRExpression> getOperands();
  List<StateExpressionClosure> getOperands(ExpressionEncoder encoder);
  StateExpressionClosure getOperand(ExpressionEncoder encoder,int i);
	IRExpression getOperand(int i);
  IRLocation getLocation();
  
  ImmutableSet<String> getPreLabels();
  ImmutableSet<String> getPostLabels();
	void setProperty(String name, Object o);
	Object getProperty(String name);
	boolean hasProperty(String name);
	boolean hasLocation();
}
