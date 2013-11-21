package edu.nyu.cascade.ir;

import xtc.tree.Node;
import xtc.tree.Printer;

public interface IREdge<Block extends IRBasicBlock> {
	void format(Printer printer);
  
	/**
	 * Get the guard expressions (may be <code>null</code>).
	 * 
	 * @return the guard expression for this edge.
	 */	
	IRBooleanExpression getGuard();
	
	/** 
	 * Get the source block of this edge 
	 * 
	 */
	Block getSource();
	
	/**
	 * Get the destination block of this edge.
	 * 
	 * @return
	 */
	Block getTarget();

	/** Get the AST node associated with the edge's guard, if any. */
	Node getSourceNode();
}
