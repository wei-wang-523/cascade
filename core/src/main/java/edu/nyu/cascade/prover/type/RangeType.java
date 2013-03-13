package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.Expression;

public interface RangeType extends Type {
  Type getBaseType();
  
  /**
   * Get the lower bound of this domain
   * @return the lower bound, null if no bound
   */
  Expression getLowerBound();
  
  /**
   * Get the upper bound of this domain
   * @return the upper bound, null if no bound
   */
  Expression getUpperBound();

}
