package edu.nyu.cascade.ir.impl;

import xtc.tree.Node;
import xtc.type.Type;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.type.IRType;

public class VarInfoFactory {
  
  /**
   * Create a variable info with declared node -- only used in sequential processor
   * @param scope
   * @param name
   * @param sourceNode
   * @return
   */
  public static IRVarInfo createVarInfoWithNode(String scope, String name, Node sourceNode) {
  	Preconditions.checkArgument(CType.hasType(sourceNode));
  	IRVarInfo varInfo = new VarInfo(scope, name, IRType.getIRType(sourceNode), sourceNode, CType.getType(sourceNode));
  	return varInfo;
  }
  
  /**
   * Create a variable info without declared node -- only scalar symbol will be set declared node later
   * @param file 
   * @param scope
   * @param name
   * @param srcType
   * @return
   */
  public static IRVarInfo createVarInfoWithType(String scope, String name, Type srcType) {
  	return new VarInfo(scope, name, IRType.getIRType(srcType), null, srcType);
  }

  /**
   * Get a copy the <code>varInfo</code> with <code>newScope</code>
   * @param file
   * @param newScope
   * @param varInfo
   * @return
   */
	public static IRVarInfo cloneVarInfoToScope(IRVarInfo varInfo, Scope newScope) {
		return new VarInfo(newScope.getQualifiedName(), varInfo.getName(), 
  					varInfo.getIRType(), varInfo.getDeclarationNode(), varInfo.getXtcType());
  }
}
