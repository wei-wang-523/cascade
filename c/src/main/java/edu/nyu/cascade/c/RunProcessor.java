package edu.nyu.cascade.c;

import edu.nyu.cascade.control.Run;

public interface RunProcessor {
  final static String TEMP_VAR_PREFIX = "cascade_tmp";
  final static String COND_ASSUME_LABEL = "COND_ASSUME";

  abstract void enableFeasibilityChecking();
  abstract boolean process(Run run) throws RunProcessorException;
  
}