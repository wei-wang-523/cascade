package edu.nyu.cascade.ir;

import java.util.List;

import xtc.tree.Node;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.ir.expr.ExpressionClosure;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.expr.PathEncoding;
import edu.nyu.cascade.prover.Expression;

public interface IRStatement {
  /**
   * Enumeration of all allowed IR nodes.
   */
  public enum StatementType {
      
      // Basic statements
      
      /** Assignment of values to a variable (set of variables) */ 
      ASSIGN,
      /** Allocate a region */
      ALLOC,
      /** Allocate an array */
      DECLARE_ARRAY,
      /** Allocate a structure */
      DECLARE_STRUCT,
      /** Field assignment a->next = b */
      FIELD_ASSIGN,
      /** Free a region in memory */
      FREE,
      /** Empty instruction node */
      SKIP,
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
      /** Call a procedure */
      CALL,
      /** Return from a procedure */
      RETURN,
      
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
  ExpressionClosure getPreCondition(ExpressionEncoder  encoder);

  /**
   * Get the strongest post-condition of the statement, using the given
   * expression factory, given a pre-condition. E.g., if the statement is
   * <code>assert x!=null</code> and the pre-condition is <code>P</code>, then
   * the post-condition will be <code>P && x!=null</code>.
   * @throws ExpressionFactoryException 
   */
  Expression getPostCondition(PathEncoding factory, Expression precondition);
  Expression getPostCondition(PathEncoding factory, Iterable<? extends Expression> precondition, 
      Iterable<? extends Expression> preGuards);
  
  StatementType getType();
  ImmutableList<IRExpression> getOperands();
  List<ExpressionClosure> getOperands(ExpressionEncoder encoder);
  ExpressionClosure getOperand(ExpressionEncoder encoder,int i);
  IRLocation getLocation();
  
  ImmutableSet<String> getPreLabels();
  ImmutableSet<String> getPostLabels();
}
