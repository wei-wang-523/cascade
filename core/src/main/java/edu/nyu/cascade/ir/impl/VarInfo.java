package edu.nyu.cascade.ir.impl;

import java.util.Map;

import com.google.common.collect.Maps;

import xtc.tree.Node;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.type.IRType;

public class VarInfo implements IRVarInfo {
  private final Scope scope;
  private final String name;
  private final IRType type;
  /**
   * The source node of the variable declaration. May not literally be a
   * Declaration node, if the variable was declared as part of a list. It
   * should, however, uniquely define the variable within the parse tree.
   */
  private final Node sourceNode;
  /** A set of client-specified properties. */
  private final Map<String,Object> properties;
  
  public VarInfo(Scope scope, String name, IRType type, Node sourceNode) {
    this.scope = scope;
    this.name = name;
    this.type = type;
    this.sourceNode = sourceNode;
    this.properties = Maps.newHashMap();
  }
  
  @Override
  public Node getDeclarationNode() {
    return sourceNode;
  }

  @Override
  public String getName() {
    return name;
  }

  @Override
  public Object getProperty(String name) {
    return properties.get(name);
  }

  @Override
  public IRType getType() {
    return type;
  }

  @Override
  public boolean hasProperty(String name) {
    return properties.containsKey(name);
  }

  @Override
  public void setProperty(String name, Object property) {
    properties.put(name, property);
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("{ name=" );
    sb.append(name);
    sb.append("; scope=" );
    sb.append(scope.getQualifiedName());
    sb.append("; type=" );
    sb.append(type);
    sb.append("; node=@" );
    sb.append(Integer.toHexString(sourceNode.hashCode()));
    for( String key : properties.keySet() ) {
      sb.append("; ");
      sb.append(key);
      sb.append("=");
      sb.append(properties.get(key));
    }
    sb.append("; }");
    return sb.toString();
  }

  @Override
  public Scope getScope() {
    return scope;
  }
}
