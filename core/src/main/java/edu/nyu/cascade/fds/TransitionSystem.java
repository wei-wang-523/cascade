package edu.nyu.cascade.fds;

import java.util.List;
import java.util.Set;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.ValidityResult;

public interface TransitionSystem {
  SatResult<?> checkSat(StateProperty p);
  ValidityResult<?> checkValidity(StateProperty p);

  /**
   * Returns a property characterizing the initial states of the system.
   */
  StateProperty initialStates() ;

  /**
   * Returns a property characterizing the side conditions (always true) of the
   * system.
   */
//  IStateProperty sideConditions() ;

  /**
   * Returns a set of properties characterizing the transition relation of the
   * system. Each property represents a single transition in the system,
   * expressed as a relation between primed and unprimed variables from the set
   * variables().
   */
  Set<? extends StateProperty> transitions() ;

  /**
   * Returns a property (a disjunction) characterizing the transition relation
   * of the system. Each disjunct will express a relation between primed and
   * unprimed variables from the set variables().
   * 
   * NOTE: The result must be equivalent to the disjunction of the properties
   * returned by transitions().
   */
  StateProperty transitionRelation();
  
  /**
   * Returns the set of state variables in the system.
   */
  Set<? extends StateVariable> variables();
  
  // FIXME: Does this belong here?
  List<Expression> stripInternalVars(List<? extends Expression> exprs);
}
