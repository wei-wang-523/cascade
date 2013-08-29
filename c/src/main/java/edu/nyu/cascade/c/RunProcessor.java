package edu.nyu.cascade.c;

import java.util.ArrayList;

import com.google.common.collect.Lists;

import edu.nyu.cascade.control.Run;

public interface RunProcessor {
  final static ArrayList<String> ReservedFunctions = 
      Lists.newArrayList("valid", "implies", "forall", "exists", "reach", 
          "allocated", "create_acyclic_list", "create_cyclic_list", 
          "create_acyclic_dlist", "create_cyclic_dlist", "is_root",
          "valid_malloc", "malloc", "free", "array_allocated", "__NONDET__");
  final static String TEMP_VAR_PREFIX = "cascade_tmp";
  final static String COND_ASSUME_LABEL = "COND_ASSUME";

  abstract void enableFeasibilityChecking();
  abstract boolean process(Run run) throws RunProcessorException;
  
}