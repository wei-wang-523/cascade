package edu.nyu.cascade.ir;

import xtc.tree.Node;
import xtc.type.Type;
import xtc.tree.Printer;
import xtc.util.SymbolTable.Scope;

public interface SymbolTable {
  void createAndEnterScope(String scopeName, Node node);
  void createScope(String scopeName, Node node);
  void define(String name, IRVarInfo info);
  // FIXME: Type of label definition?
  void defineLabel(String name, Object def);
  void enterScope(IRControlFlowGraph cfg);
  void enterScope(Node node);
  void format(Printer printer);
  Scope getCurrentScope();
  Scope getScope(Node node);
  Scope getScope(String id);
  boolean hasScope(Node node);
  boolean isDefined(String name);
  boolean isDefined(String name, String namespace);
  boolean labelIsDefined(String name);
  IRVarInfo lookup(String name);
  Scope lookupScope(String name);
  String qualify(String parameter);
  Scope rootScope();
  void setScope(Scope scope);
  String toLabelName(String name);
  String toNamespace(String name, String namespace);
  void undefine(String name);
  xtc.util.SymbolTable toXtcSymbolTable();
  xtc.util.SymbolTable getOriginalSymbolTable();
  Type lookupType(String name);
	void enter(String name);
	void exit();
}
