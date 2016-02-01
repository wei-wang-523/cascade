package edu.nyu.cascade.ir.impl;

import java.util.Map;

import com.google.common.collect.Maps;

import xtc.tree.Node;
import xtc.type.Type;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.HashCodeUtil;

public class VarInfo implements IRVarInfo {	
  private final String scope;
  private final String name;
  private final IRType type;
  private final Type sourceType;
  private Expression lBinding, rBinding;
  
  /** A set of client-specified properties. */
  private final Map<String,Object> properties;
  
  /**
   * The source node of the variable declaration. May not literally be a
   * Declaration node, if the variable was declared as part of a list. It
   * should, however, uniquely define the variable within the parse tree.
   */
  private Node sourceNode;
  
  VarInfo(String scope, String name, IRType type, Node sourceNode, Type sourceType) {
    this.scope = scope;
    this.name = name;
    this.type = type;
    this.sourceNode = sourceNode;
    this.sourceType = sourceType;
    this.properties = Maps.newHashMap();
  }
  
  @Override
  public void setDeclarationNode(Node node) {
  	sourceNode = node;
  }
  
  @Override
  public Type getXtcType() {
  	return sourceType;
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
  public IRType getIRType() {
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
    sb.append(scope);
    sb.append("; type=" );
    sb.append(type);
    sb.append("; xtcType=" );
    sb.append(sourceType);
    sb.append("; isDeclared=" );
    sb.append(sourceNode != null);
    if(sourceNode != null) {
      sb.append("; node=@" );
      sb.append(Integer.toHexString(sourceNode.hashCode()));
    }
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
  public String getScopeName() {
    return scope;
  }

	@Override
  public Expression getLValBinding() {
	  return lBinding;
  }

	@Override
  public Expression getRValBinding() {
	  return rBinding;
  }
	
	@Override
	public boolean hasLValBinding() {
		return lBinding != null;
	}
	
	@Override
	public boolean hasRValBinding() {
		return rBinding != null;
	}

	@Override
  public void setLValBinding(Expression varExpr) {
		this.lBinding = varExpr;
  }
	
	@Override
  public void setRValBinding(Expression varExpr) {
		this.rBinding = varExpr;
  }
	
	@Override
	public int hashCode() {
		return HashCodeUtil.hash(
				HashCodeUtil.hash(
						HashCodeUtil.hash(HashCodeUtil.SEED, name), 
						scope), 
						sourceType.resolve());
	}

	@Override
  public long getSize() {
		return CType.getSizeofType(sourceType);
  }
}
