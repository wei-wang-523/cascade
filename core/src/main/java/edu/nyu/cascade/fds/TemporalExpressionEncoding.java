package edu.nyu.cascade.fds;

import com.google.common.base.Function;

import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.prover.Expression;

/**
 * An encoding of temporal expressions on program states, parameterized by the
 * underlying encoding of program state. This extends the normal expression
 * encoding with predicates testing the current program location ("at"
 * predicates) and asserting the state is unchanged by the execution of 
 * a statement ("preserved"). It also overrides several ExpressionEncoding
 * mthods to return StateExpressions and StateProperties.
 * 
 * TODO(cconway): I've added the overrides on an as-needed basis, so they don't
 * cover the whole interface.
 */

public interface TemporalExpressionEncoding extends ExpressionEncoding {
  public static interface Factory {
    TemporalExpressionEncoding create(ExpressionEncoding baseEncoding);
  }
  
  /** Add an "at predicate" for a label in a parameterized system. Implementations
   * may choose how to represent such a parameterized predicate, but it should
   * be a function from an integer index to boolean (both <code>Expr</code>'s).
   */
  void addAtPredicate(String label, Function<StateExpression,StateExpression> atPred);

  /* [chris 10/24/2009] FIXME: Keeping track of "at" predicates here isn't very
   * clean. For one thing, it means that we have to thread the same factory 
   * through the whole program, so that the predicates added by the FDSBuilder 
   * are available later for building assertions. */
  /** Add a boolean "at predicate" for a label in the CFG. */
  void addAtPredicate(String label, StateExpression atPred) throws ExpressionFactoryException;
  
  @Override
  StateProperty and(Expression... conjuncts);

  /**
   * Returns a boolean expression representing the conjunction of the two
   * boolean arguments.
   */
  @Override
  StateProperty and(Expression lhs, Expression rhs) ;

  @Override
  StateProperty and(Iterable<? extends Expression> conjuncts) ;

  /**
   * Retrieve an "at predicate" for a label in a parameterized system, given the
   * name of the label and an index variable.
   */
  StateProperty atPredicate(StateExpression index, String firstLabel, String... otherLabels) throws ExpressionFactoryException;

  /** Retrieve an "at predicate" for a label in the CFG, given the name of the label. */
  StateProperty atPredicate(String firstLabel, String... otherLabels) throws ExpressionFactoryException;

  
  @Override
  StateExpression bindingForSourceVar(String qName);
  
  @Override
  StateProperty castToBoolean(Expression Expression) ;
  @Override
  StateProperty eq(Expression a, Expression b);
  @Override
  IntegerStateExpression integerConstant(int i);
  StateProperty preserved(Iterable<? extends StateVariable> xs)
      throws ExpressionFactoryException;
  @Override
  StateVariable symbolicConstant(String name, IRType t, boolean fresh);
  @Override
  StateVariable variable(String name, IRType type, boolean fresh);

}
