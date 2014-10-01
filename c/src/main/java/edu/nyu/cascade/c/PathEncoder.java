package edu.nyu.cascade.c;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.expr.PathFactoryException;

public interface PathEncoder<T> {
  
  boolean runIsFeasible() throws PathFactoryException;

  /**
   * Returns true if all verification conditions passed to handle() since the
   * last call to reset() were valid.
   */
  boolean runIsValid();
  
  /**
   * Returns true if the labeled block is reachable
   */
	boolean runIsReachable();
  
  void setFeasibilityChecking(boolean b);
  
  /**
   * Prepare this encoder for a new path.
   */
  void reset();

	void encode(PreProcessor<?> preprocessor, T graph)
      throws PathFactoryException;

	void checkReach(PreProcessor<?> preprocessor, T graph, String label)
      throws PathFactoryException;
	
	void checkReachIncremental(PreProcessor<?> preprocessor, T graph, String label)
			throws PathFactoryException;
}
