package edu.nyu.cascade.ir;

import xtc.tree.Node;

import com.google.common.collect.ImmutableSet;

public interface IRCallGraphNode {
	
  void addCalledFunction(IRCallGraphNode function);

  ImmutableSet<? extends IRCallGraphNode> getCalledFunctions();

  /**
   * Get the function declaration node
   * @return
   */
  Node getFuncDeclareNode();
  
  /**
   * Return the function name that this call graph node represents.
   * @return
   */
  String getName();
  
  /**
   * Return the scope of the function
   */
  String getScopeName();
}
