/**
 * This program is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General License as published by
 * the Free Software Foundation, either version 3 of the License, or (at your
 * option) any later version.
 * 
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General License
 * for more details.
 * 
 * You should have received a copy of the GNU Lesser General License
 * along with this program. If not, see <http://www.gnu.org/licenses/>
 */
package edu.nyu.cascade.ir;

import java.util.Collection;
import java.util.Set;

import xtc.tree.Location;
import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable.Scope;

/**
 * Provides an intermediate representation that allows access to the
 * instructions/statements of a method/function independently of the language
 * used [as much as possible :)].
 */
public interface IRControlFlowGraph {
	
	Collection<? extends IREdge<? extends IRBasicBlock>> getEdges();
  
  /** Get the initial node. The initial node has no predecessors and no statements. */
  IRBasicBlock getEntry();

  /** Get the exit node. The exit node has no successors and no statements. */
  IRBasicBlock getExit();

  /** Get all the nodes in the CFG representation. */
  Set<? extends IRBasicBlock> getBlocks();

  /** Get the predecessors for the given <code>block</code>. */
  Set<? extends IRBasicBlock> getPredecessors(IRBasicBlock block);

  /** Get the successors for the given <code>block</code>. */
  Set<? extends IRBasicBlock> getSuccessors(IRBasicBlock block);

  /** Get the list of incoming edges. */
  Collection<? extends IREdge<? extends IRBasicBlock>> getIncomingEdges(
      IRBasicBlock block);

  /** Get the list of outgoing edges. */
  Collection<? extends IREdge<? extends IRBasicBlock>> getOutgoingEdges(
      IRBasicBlock block);

  Scope getScope();

  /** Get the source node of the declaration for this CFG. */
  Node getSourceNode();

  /** Get the source location of the declaration for this CFG. */
  Location getLocation();
  
  /** Get the name of this CFG (e.g., the name of the procedure). */
  String getName();

  /** Pretty-print the CFG to the given <code>Printer</code>. */
  void format(Printer printer);

	void removeBlock(IRBasicBlock block);

	void removeEdge(IREdge<?> edge);

	void addEdge(IREdge<?> edge);

	void addEdge(IRBasicBlock currentBlock, IRBasicBlock succ);

	void addEdge(IRBasicBlock source, IRBooleanExpression guard, IRBasicBlock target);

	void setEntry(IRBasicBlock newEntry);
	
	void setExit(IRBasicBlock newExit);

	Collection<IRBasicBlock> topologicalSeq(IRBasicBlock startBlock);

	IRControlFlowGraph clone();
}
