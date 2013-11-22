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
   * Set the function declaration node
   * @return
   */
  void setFuncDeclareNode(Node def);
  
  /**
   * Get the function definition node
   * @return
   */
	Node getFuncDefinitionNode();
	
  /**
   * Set the function definition node
   * @return
   */
	void setFuncDefinitionNode(Node decl);
  
  /**
   * Return the function name that this call graph node represents.
   * @return
   */
  String getName();
  
  /**
   * Return the scope of the function
   */
  String getScopeName();

	boolean isDefined();

	boolean isDeclared();

	/**
	 * Get the signature of function
	 * @return
	 */
	IRVarInfo getSignature();

}
