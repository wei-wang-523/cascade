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
	
	Expression getLValBinding();
	boolean hasLValBinding();
	
	/**
	 * Set the left binding expression to var info.
	 * @param varExpr
	 */
	void setLValBinding(Expression varExpr);
	
  boolean hasProperty(String name);
  void setProperty(String name, Object property);
	void setDeclarationNode(Node node);
	
	void enableLogicLabel();
	void disableLogicLabel();
	boolean hasLogicLabel();
	
	boolean isDeclared();
  
  boolean isStatic();
}
