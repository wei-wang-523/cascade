package edu.nyu.cascade.c;

import edu.nyu.cascade.control.Run;

public interface RunProcessor {
	
	void enableFeasibilityChecking();
  
  /**
   * Process a run: build the path through the CFG that it represents, convert
   * the path to a verification condition, then check the verification
   * condition.
   * 
   * @param run
   *          a run from a Cascade control file
   * @return true if all assertions in the run hold, false otherwise.
   * @throws RunProcessorException
   *           if an error occurred while processing the run. E.g., if the path
   *           was ill-defined, or if an unhandled statement was encountered.
   */
	boolean process(Run run) throws RunProcessorException;
  
}