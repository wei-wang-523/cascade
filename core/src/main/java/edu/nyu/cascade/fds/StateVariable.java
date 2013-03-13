package edu.nyu.cascade.fds;

import edu.nyu.cascade.prover.VariableExpression;

public interface StateVariable extends
    VariableExpression, StateExpression {

  /**
   * Returns true if this variable is "primed".
   */
  boolean isPrimed();

  /**
   * Returns the primed version of the formula.
   */
  StateVariable prime() ;

  /**
   * Returns the unprimed version of the formula.
   */
  StateVariable unprime();

  /**
   * Returns the state property that holds when the prime and unprimed versions
   * of this variable are equal. (PRE: should be unprimed?)
   */
  StateProperty preserved() ;
}
