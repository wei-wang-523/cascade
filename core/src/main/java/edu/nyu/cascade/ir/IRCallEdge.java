package edu.nyu.cascade.ir;

import xtc.tree.Node;
import xtc.tree.Printer;

public interface IRCallEdge <CallGraphNode extends IRCallGraphNode>{
  
  void format(Printer printer);
	
	/** 
	 * Get the source node of this edge 
	 * 
	 */
	IRCallGraphNode getSource();
	
	/**
	 * Get the destination node of this edge.
	 * 
	 * @return
	 */
	IRCallGraphNode getTarget();

	/** Get the AST node associated with the edge's guard, if any. */
	Node getCallNode();
}
