package edu.nyu.cascade.ir;

import java.util.Set;

import xtc.tree.Node;
import xtc.tree.Printer;

/**
 * Provides an intermediate representation that allows access to the
 * instructions/statements of a method/function independently of the language
 * used [as much as possible :)].
 */
public interface IRCallGraph {
  /**
   * Get all the nodes in the Call Graph representation.
   * 
   * @return list of all nodes
   */
  Set<? extends IRCallGraphNode> getNodes();

  /** Get the predecessors for the given <code>node</code>. */
  Set<? extends IRCallGraphNode> getPredecessors(IRCallGraphNode node);

  /** Get the successors for the given <code>node</code>. */
  Set<? extends IRCallGraphNode> getSuccessors(IRCallGraphNode node);

  /**
   * Get the list of incoming edges.
   * 
   * @return the list of incoming edges.
   */
  Set<? extends IRCallEdge<? extends IRCallGraphNode>> getIncomingEdges(IRCallGraphNode node);

  /**
   * Get the list of outgoing edges.
   * 
   * @return the list of outgoing edges.
   */
  Set<? extends IRCallEdge<? extends IRCallGraphNode>> getOutgoingEdges(IRCallGraphNode node);

  /** Pretty-print the Call Graph to the given <code>Printer</code>. */
  void format(Printer printer);

  /** Get callee function node */
	IRCallGraphNode getCallee(IRCallGraphNode funcNode, Node node);
	
  /** Get caller function node */
	IRCallGraphNode getCaller(IRCallGraphNode funcNode, Node node);

	/** Decide if has caller function */
	boolean hasCallee(IRCallGraphNode funcNode, Node node);
	
	/** Decide if has caller function */
	boolean hasCaller(IRCallGraphNode funcNode, Node node);
}
