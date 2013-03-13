package edu.nyu.cascade.ir;

import xtc.tree.Node;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.ir.type.IRType;

public interface IRVarInfo {
  Node getDeclarationNode();
  String getName();
  Object getProperty(String name);
  Scope getScope();
  IRType getType();
  boolean hasProperty(String name);
  void setProperty(String name, Object property);
}
