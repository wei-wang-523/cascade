package edu.nyu.cascade.prover;

import com.google.common.collect.ImmutableList;

/**
 * The interface that tags the expression as a Boolean expression. Methods for
 * all operations on Booleans are provided. These methods should use the same
 * expression manager that the expression itself is using.
 * 
 * @author <a href="mailto:dejan@cs.nyu.edu">Dejan Jovanović</a>
 */
public interface BooleanExpression extends Expression {
  /**
   * Add a trigger pattern p to a quantified expression. A trigger pattern is a
   * term or atomic predicate that is a sub-expression of this expression. The
   * free variables of p will be used to instantiate the quantified variables of
   * this expression during query processing. p will be added to the end of the
   * list of triggers for e, i.e., it will be matched last.
   * 
   * Concrete implementations of IBooleanExpression may ignore triggers.
   * */
  void addTrigger(Expression p) ;
  
  /**
   * Add a no trigger pattern p to a quantified expression. A trigger pattern is a
   * term or atomic predicate that is a sub-expression of this expression. The
   * free variables of p will not be used to instantiate the quantified variables of
   * this expression during query processing. p will be added to the end of the
   * list of noTriggers for e, i.e., it will be matched last.
   * 
   * Concrete implementations of IBooleanExpression may ignore noTriggers.
   * */
  void addMultiTrigger(Iterable<? extends Expression> multiTrigger);
  
  /**
   * Returns a new Boolean expression that is the conjunction of this expression
   * and the given Boolean expression <code>e</code>
   * 
   * @param e
   *          expression to conjunct
   * @return the conjunction
   */
  BooleanExpression and(Expression e) ;
  BooleanExpression and(Iterable<? extends Expression> e) ;

  /**
   * Existentially quantify the given variables.
   * 
   * @param vars
   *          the variables to quantify out
   * @return a new existential expression
   */
  BooleanExpression exists(Iterable<? extends Expression> vars) ;
  BooleanExpression exists(Expression firstVar, Expression... otherVars) ;

  /**
   * 
   * Universally quantify the given variables.
   * 
   * @param vars
   *          the variables to quantify out
   * @param body
   *          the expression to quantify
   * @return a new universal expression
   */
  BooleanExpression forall(Iterable<? extends Expression> vars) ;
  BooleanExpression forall(Expression firstVar, Expression... otherVars) ;

  Kind getKind();
  /**
   * Get the collection of trigger patterns for a quantified expression. */
  ImmutableList<ImmutableList<? extends Expression>> getTriggers() ;

  /**
   * Returns a new Boolean expression that is the equivalence of this expression
   * and the given Boolean expression <code>e</code>
   * 
   * @param e
   *          Boolean expression
   * @return the equivalence
   */
  public BooleanExpression iff(Expression e) ;

  Expression ifThenElse(Expression thenPart, Expression elsePart);

  /**
   * Returns a new Boolean expression that is the implication of this expression
   * and the given Boolean expression <code>e</code>
   * 
   * @param e
   *          expression to imply
   * @return the implication
   */
  public BooleanExpression implies(Expression e) ;

  /**
   * Returns a new Boolean expression that is the negation of this expression.
   * 
   * @return the negation
   */
  public BooleanExpression not() ;

  /**
   * Returns a new Boolean expression that is the disjunction of this expression
   * and the given Boolean expression <code>e</code>
   * 
   * @param e
   *          expression to disjunct
   * @return the disjunction
   */
  public BooleanExpression or(Expression e) ;

  /**
   * Add a collection of triggers patterns to a quantified expression. A trigger
   * pattern p is a term or atomic predicate that contains a free reference to a
   * bound variable x in this expression. Terms of the form p[t/x] will trigger
   * an instantiation of x with t during query processing. The trigger patterns
   * will matched in the order they appear in the Iterable.
   * 
   * Concrete implementations of IBooleanExpresison may ignore triggers.
   */
  void setTriggers(Iterable<? extends Expression> triggers) ;
  /**
   * Add a collection of multi-trigger patterns to a quantified expression. A
   * multi-trigger pattern m is a set of trigger patterns that must all be
   * matched before instantiation. The multi-trigger patterns will matched in
   * the order they appear in the Iterable.
   * 
   * Concrete implementations of IBooleanExpresison may ignore triggers.
   */
  void setMultiTriggers(Iterable<? extends Iterable<? extends Expression>> multiTriggers) ;
  
  /**
   * Returns a new Boolean expression that is the exclusive or (xor) of this
   * expression and the given Boolean expression <code>e</code>
   * 
   * @param e
   *          expression to xor
   * @return the xor
   */
  public BooleanExpression xor(Expression e) ;

  BooleanExpression or(Iterable<? extends Expression> disjuncts) ;

  /**
   * Returns a new Boolean expression that is the integer representation of this
   * expression.
   * 
   * @return the integer cast
   */
  // public IIntegerExpression castToInteger();

  /**
   * Returns a new Boolean expression that is the rational representation of
   * this expression.
   * 
   * @return the rational cast
   */
  // public IRationalExpression castToRational();
}
