package edu.nyu.cascade.prover.type;

import com.google.common.collect.ImmutableList;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public interface BooleanType extends Type, ScalarType {
  /**
   * Add a trigger pattern p to quantified expression e. A trigger pattern is a
   * term or atomic predicate that is a sub-expression of e. The free variables
   * of p will be used to instantiate the quantified variables of e during query
   * processing. p will be added to the end of the list of triggers for e, i.e.,
   * it will be matched last.
   * 
   * Concrete implementations of IBooleanType may ignore triggers.
   * */
  void addTrigger(Expression e, Expression p);

  /**
   * Returns a new Boolean expression that is the conjunction of this expression
   * and the given Boolean expression <code>e</code>
   * 
   * @param e
   *          expression to conjunct
   * @return the conjunction
   */
  BooleanExpression and(Expression a, Expression b);

  BooleanExpression and(Expression first, Expression... rest);

  /**
   * Create a new Boolean AND expression given a list of subexpressions.
   * 
   * @param subExpressions
   *          the list of subexpressions to use
   * @return the and of left and right
   */
  BooleanExpression and(Iterable<? extends Expression> subExpressions);

  /**
   * Given a boolean expression and a list of variables, create the existential
   * quantification of the variables over the body.
   * 
   * @param vars
   *          the variables to quantify out
   * @param body
   *          the expression to quantify
   * @return a new existential expression
   */
  BooleanExpression exists(Iterable<? extends Expression> vars,
      Expression body);
  
  BooleanExpression exists(Iterable<? extends Expression> vars,
      Expression body, Iterable<? extends Expression> triggers);

  BooleanExpression exists(Iterable<? extends Expression> vars,
      Expression body, Iterable<? extends Expression> triggers, 
      Iterable<? extends Expression> noTriggers);

  /**
   * Given a boolean expression and a list of variables, create the universal
   * quantification of the variables over the body.
   * 
   * @param vars
   *          the variables to quantify out
   * @param body
   *          the expression to quantify
   * @return a new universal expression
   */
  BooleanExpression forall(Iterable<? extends Expression> vars,
      Expression body);

  BooleanExpression forall(Iterable<? extends Expression> vars,
      Expression body, Iterable<? extends Expression> triggers);

  BooleanExpression forall(Iterable<? extends Expression> vars,
      Expression body, Iterable<? extends Expression> triggers, 
      Iterable<? extends Expression> noTriggers);
  
  /**
   * Get the collection of trigger patterns for a quantified expression.
   */
  ImmutableList<ImmutableList<? extends Expression>> getTriggers(Expression e);

  BooleanExpression ff();

  /**
   * Returns a new Boolean expression that is the equivalence of this expression
   * and the given Boolean expression <code>e</code>
   * 
   * @param e
   *          Boolean expression
   * @return the equivalence
   */
  BooleanExpression iff(Expression a, Expression b);
  
  /**
   * Wrap arg as rewrite rule
   * 
   * @param a, b, c
   * @return the rewrite rule
   */
  BooleanExpression rewriteRule(Iterable<? extends Expression> vars, 
      Expression guard, Expression body);
  
  /**
   * RR_REWRITE rule (equality)
   * 
   * @param head, body, triggers
   * @return the rule
   */
  BooleanExpression rrRewrite(Expression head, Expression body, Iterable<? extends Expression> triggers);
  
  BooleanExpression rrRewrite(Expression head, Expression body);
  
  /**
   * RR_REDUCTION rule
   * 
   * @param head, body
   * @return the rule
   */
  BooleanExpression rrReduction(Expression head, Expression body, Iterable<? extends Expression> triggers);
  
  BooleanExpression rrReduction(Expression head, Expression body);
  
  /**
   * RR_DEDUCTION rule
   * 
   * @param head, body
   * @return the rule
   */
  BooleanExpression rrDeduction(Expression head, Expression body, Iterable<? extends Expression> triggers);
  
  BooleanExpression rrDeduction(Expression head, Expression body);

  Expression ifThenElse(Expression cond, Expression thenPart,
      Expression elsePart);

  /**
   * Returns a new Boolean expression that is the implication of this expression
   * and the given Boolean expression <code>e</code>
   * 
   * @param e
   *          expression to imply
   * @return the implication
   */
  BooleanExpression implies(Expression a, Expression b);

  /**
   * Returns a new Boolean expression that is the negation of this expression.
   * 
   * @return the negation
   */
  BooleanExpression not(Expression a);

  /**
   * Returns a new Boolean expression that is the disjunction of this expression
   * and the given Boolean expression <code>e</code>
   * 
   * @param e
   *          expression to disjunct
   * @return the disjunction
   */
  BooleanExpression or(Expression a, Expression b);

  BooleanExpression or(Iterable<? extends Expression> subExpressions);

  BooleanExpression or(Expression... subExpressions);

  /**
   * Add a collection of triggers patterns to quantified expression e. A trigger
   * pattern p is a term or atomic predicate that is a sub-expression of e. The
   * free variables of p will be used to instantiate the quantified variables of
   * e during query processing. The trigger patterns will matched in the order
   * they appear in the Iterable.
   * 
   * Concrete implementations of IExpressionManager may ignore triggers.
   * */
  void setTriggers(Expression e, Iterable<? extends Expression> triggers);

  BooleanExpression tt();

  /**
   * Returns a new Boolean expression that is the exclusive or (xor) of this
   * expression and the given Boolean expression <code>e</code>
   * 
   * @param e
   *          expression to xor
   * @return the xor
   */
  BooleanExpression xor(Expression a, Expression b);
  
  /**
   * Return a Boolean variable with <code>name</code>
   */
  @Override
  BooleanExpression variable(String name, boolean fresh);
  
  /**
   * Return a bound Boolean variable with <code>name</code> used for
   * quantified expression
   */
  @Override
  BooleanExpression boundVar(String name, boolean fresh);

  /**
   * Return a bound Boolean variable with <code>name</code> used for
   * quantified expression
   */
  @Override
  BooleanExpression boundExpression(String name, int index, boolean fresh);
  
  /**
   * Create an expression stating that all of the children are pairwise
   * distinct. I.e., the expression created by
   * <code>distinctExpression(args)</code>
   * 
   * @param args
   *          the arguments
   * @return a boolean expression representing the assertion that the arguments
   *         are pairwise distinct
   */
	BooleanExpression distinct(Iterable<? extends Expression> args);

  /**
   * Create an expression stating that all of the children are pairwise
   * distinct. I.e., the expression created by
   * <code>distinctExpression(args)</code>
   * 
   * @param first
   *          the first argument
   * @param second
   *          the second argument
   * @param rest
   *          the remainder of the arguments
   * @return a boolean expression representing the assertion that the arguments
   *         are pairwise distinct
   */
	BooleanExpression distinct(Expression first, Expression second,
      Expression... rest);

  /**
   * Create a new equality expression
   * 
   * @param left
   *          the left operand
   * @param right
   *          the right operand
   * @return the or of left and right
   */
	BooleanExpression eq(Expression left, Expression right);
}
