package edu.nyu.cascade.fds;


import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public interface StateProperty extends StateExpression, BooleanExpression {
  public static interface Factory {
    StateProperty valueOf( Expression expr );
  }
  
  @Override
  StateProperty and(Expression p);
  
  /** Returns the conjunction of this property with conjuncts. */
  StateProperty and(StateProperty... conjuncts) ;

  /** Returns the conjunction of this property with conjuncts. */
  @Override
  StateProperty and(Iterable<? extends Expression> conjuncts) ;

  /** Checks satisfiability of the property. */
//  SatResult<?> checkSat() ;

  /** Checks the validity of the property. */
//  ValidityResult<?> checkValidity() ;

//  StateProperty exists(VariableExpression j);
  
  /**
   * Returns a quantified version of the property, where the given variables are
   * existentially quantified.
   */

  @Override
  StateProperty exists(Iterable<? extends Expression> vars) ;
  @Override
  StateProperty exists(Expression firstVar, Expression... otherVars) ;

  ImmutableSet<StateVariable> getVariables() ;
  
//  StateProperty forall(VariableExpression j);

  /**
   * Returns a quantified version of the property, where the given variables are
   * universally quantified.
   */
  StateProperty forall(Iterable<? extends Expression> vars) ;
  @Override
  StateProperty forall(Expression firstVar, Expression... otherVars) ;

  @Override
  StateProperty iff(Expression p) ;
  
  @Override
  StateExpression ifThenElse(Expression thenPart, Expression elsePart);

  /** Returns the property stating that this property implies p. */
  @Override
  StateProperty implies(Expression p) ;

  /** Returns the negation of the property. */
  @Override
  StateProperty not() ;

  @Override
  StateProperty or(Expression p);
  
  /** Returns the disjunction of this property with disjuncts. */
  StateProperty or(StateProperty... disjuncts) ;

  /** Returns the disjunction of this property with disjuncts. */
  @Override
  StateProperty or(Iterable<? extends Expression> disjuncts) ;

  /**
   * Returns the primed version of the property. (PRE: All variables should be
   * unprimed?)
   */
  @Override
  StateProperty prime() ;

  BooleanExpression toBooleanExpression();
  
  /**
   * Returns the unprimed version of the property. (PRE: All variables should be
   * primed?)
   */
  @Override
  StateProperty unprime() ;

  @Override
  StateProperty xor(Expression p) ;

  @Override
  BooleanExpression toExpression();

}
