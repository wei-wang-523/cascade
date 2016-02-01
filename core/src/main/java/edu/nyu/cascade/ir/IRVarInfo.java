package edu.nyu.cascade.ir;

import xtc.tree.Node;
import xtc.type.Type;
import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.prover.Expression;

public interface IRVarInfo {
  Node getDeclarationNode();
  String getName();
  Object getProperty(String name);
  String getScopeName();
  IRType getIRType();
	Type getXtcType();
	long getSize();
	
	Expression getLValBinding();
	Expression getRValBinding();

	boolean hasLValBinding();
	boolean hasRValBinding();
	
	/**
	 * Set the left binding expression to var info, if the var info has 
	 * a region var info attached (created by Steensgaard analysis),
	 * set the <code>varExpr</code> to region var info too.
	 * @param varExpr
	 */
	void setLValBinding(Expression varExpr);
	void setRValBinding(Expression varExpr);
	
  boolean hasProperty(String name);
  void setProperty(String name, Object property);
	void setDeclarationNode(Node node);
}
