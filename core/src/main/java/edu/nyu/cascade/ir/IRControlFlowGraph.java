/**
 * This program is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or (at your
 * option) any later version.
 * 
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
 * for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>
 */
package edu.nyu.cascade.ir;

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
  public Scope getDefiningScope();
  
  /**
   * Get the initial node. The initial node has no predecessors and no statements.
   */
  public IRBasicBlock getEntry();

  /**
   * Get the exit node. The exit node has no successors and no statements.
   */
  public IRBasicBlock getExit();

  /**
   * Get all the nodes in the CFG representation.
   * 
   * @return list of all nodes
   */
  public Set<? extends IRBasicBlock> getBlocks();

  /** Get the predecessors for the given <code>block</code>. */
  public Set<? extends IRBasicBlock> getPredecessors(IRBasicBlock block);

  /** Get the successors for the given <code>block</code>. */
  public Set<? extends IRBasicBlock> getSuccessors(IRBasicBlock block);

  /**
   * Get the list of incoming edges.
   * 
   * @return the list of incoming edges.
   */
  public Set<? extends IREdge<? extends IRBasicBlock>> getIncomingEdges(
      IRBasicBlock block);

  /**
   * Get the list of outgoing edges.
   * 
   * @return the list of outgoing edges.
   */
  public Set<? extends IREdge<? extends IRBasicBlock>> getOutgoingEdges(
      IRBasicBlock block);

  public Scope getScope();
  
  public IRBasicBlock bestBlockForPosition(IRLocation loc);

  /**
   * Alters the CFG, if necessary, so that <code>location</code> lies between
   * two basic blocks. If the edge connecting the two blocks is guarded, then
   * the position will lie between the guard and the target block. Returns the
   * block that immediately follows the position. If the location exactly
   * coincides with a source line and the parameter <code>insertBefore</code> is
   * true, then the CFG will be split <em>before</em> the source line; otherwise,
   * it will be split <em>after</em> the source line.
   * 
   * If <code>getSucc</code> is false, return the block before the position
   * 
   * Returns <code>null</code> if the CFG cannot be split at <code>position</code>.
   */
  public IRBasicBlock splitAt(IRLocation position, boolean insertBefore, boolean getSucc);
  
  /** Equivalent to <code>splitAt(location,insertBefore,true)</code> */
  public IRBasicBlock splitAt(IRLocation location, boolean insertBefore);
  
  /** Equivalent to <code>splitAt(location,true)</code> */
  public IRBasicBlock splitAt(IRLocation location);

  /** Get the source node of the declaration for this CFG. */
  Node getSourceNode();

  /** Get the source location of the declaration for this CFG. */
  Location getLocation();

  // File getFile();
  /** Get the name of this CFG (e.g., the name of the procedure). */
  String getName();

  /** Pretty-print the CFG to the given <code>Printer</code>. */
  void format(Printer printer);

}
