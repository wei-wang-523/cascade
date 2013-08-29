package edu.nyu.cascade.c;

import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.PathFactoryException;

public interface PathEncoder {
  final static String COND_ASSUME_LABEL = "COND_ASSUME";
  
  boolean runIsFeasible() throws PathFactoryException;

  /**
   * Returns true if all verification conditions passed to handle() since the
   * last call to reset() were valid.
   */
  boolean runIsValid();
  
  void setFeasibilityChecking(boolean b);
  
  /**
   * Prepare this encoder for a new path.
   */
  void reset();
  
  ExpressionEncoder getExpressionEncoder();
}
