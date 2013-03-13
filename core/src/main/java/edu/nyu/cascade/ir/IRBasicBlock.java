package edu.nyu.cascade.ir;

import java.util.List;

import xtc.tree.Node;
import xtc.util.SymbolTable.Scope;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

public interface IRBasicBlock {

  public static enum Type {
    /** A standard block, with a non-branching list of statements. */
    BLOCK,
    /**
     * A loop header. The block has no statements and two successors: the body
     * of the loop and its exit.
     */
    LOOP,
    /**
     * A switch block. The block has no statements and N successors, one for
     * each case label.
     */
    SWITCH,
    /**
     * A call block. The block has a single statement (the call) and a single
     * successor.
     */
    CALL,
    /** An entry block. The block has no statements and one successor. */
    ENTRY,
    /** An exit block. The block has no statements and no successors. */
    EXIT ;
  }

  void addPreLabel(String label);
  void addPostLabel(String label);
  void addStatements(List<? extends IRStatement> postStatements);
  /**
   * Return the IR responsible for this node
   * 
   * @return the IR responsible for this node.
   */
  ImmutableList<? extends IRStatement> getStatements();

  Node getStartNode();

  IRLocation getStartLocation();
  IRLocation getEndLocation();
  
  /** Add a "virtual" location (i.e., one not associated with a statement) to this block. 
   * This is useful for for making sure if and loop tests have an associated location.
   * 
   * @param loc the location to add to this block
   */
  void addLocation(IRLocation loc);

  Type getType();
  
  int getIterTimes();
  
  void clearIterTimes();
  
  /** Returns true if the start and end location are defined for this block. */
  boolean hasLocation();
  
  /**
   * Split a block around a source position. A new (possibly empty) block will
   * be created, with the statements from this block that come after the position.
   * Returns the new block.
   */
  IRBasicBlock splitBefore(IRLocation position);
  IRBasicBlock splitAfter(IRLocation position);
  
  ImmutableSet<String> getPreLabels();
  ImmutableSet<String> getPostLabels();
  
  void setScope(Scope scope);
  Scope getScope();
}
