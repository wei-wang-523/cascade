package edu.nyu.cascade.c.preprocessor.typeanalysis;

import xtc.tree.Node;
import xtc.type.Type;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.c.preprocessor.IRVar;

public class IRVarImpl implements IRVar {
	private final String name;
	private final Type type;
	private final Scope scope;
	private final Node srcNode;
	
	private IRVarImpl(String _name, Node _srcNode, Type _type, Scope _scope) {
		name = _name;
		srcNode = _srcNode;
		scope = _scope;
		type = _type;
	}
	  
	protected static IRVarImpl createWithSrcNode(String _name, Node _srcNode, Type _type, Scope _scope) {
		return new IRVarImpl(_name, _srcNode, _type, _scope);
	}
	
	protected static IRVarImpl create(String _name, Type _type, Scope _scope) {
		return new IRVarImpl(_name, null, _type, _scope);
	}

	
	@Override
	public String getName() {
		return name;
	}

	@Override
	public Type getType() {
		return type;
	}
	
	@Override
  public boolean equals(Object o) {
    if(!(o instanceof IRVarImpl)) return false;
    IRVarImpl var = (IRVarImpl) o;
    return name.equals(var.getName()) && type == var.getType() && scope.equals(var.getScope()) && srcNode.equals(var.getNode());
  }

	@Override
	public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append(name);
    if(scope != null) 
      sb.append('@').append(scope.getName());
    if(type != null)
      sb.append("(type ").append(type.getName()).append(") ");
    return sb.toString();
  }

	@Override
	public String toStringShort() {
	  StringBuilder sb = new StringBuilder().append(name);
	  if(scope != null)  sb.append(scope.getQualifiedName());
	  return sb.toString();
	}
	
	@Override
	public Scope getScope() {
		return this.scope;
	}

	protected Node getNode() {
		return srcNode;
	}

	protected boolean hasNode() {
		return srcNode != null;
	}
}
