package edu.nyu.cascade.ir;

import java.io.File;
import java.util.Set;

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
  Set<? extends IRCallEdge<IRCallGraphNode>> getIncomingEdges(IRCallGraphNode node);

  /**
   * Get the list of outgoing edges.
   * 
   * @return the list of outgoing edges.
   */
  Set<? extends IRCallEdge<IRCallGraphNode>> getOutgoingEdges(IRCallGraphNode node);

  /** Pretty-print the Call Graph to the given <code>Printer</code>. */
  void format(Printer printer);

  /**
   * Get the source file of the Call Graph
   * 
   * @return the source file
   */
  File getFile();
}
