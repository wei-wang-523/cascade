package edu.nyu.cascade.c.preprocessor.typeanalysis;

import xtc.type.Type;
import edu.nyu.cascade.c.preprocessor.IRVar;

public class IRVarImpl implements IRVar {
	private final String name;
	private final Type type;
	private final String scope;
	
	private IRVarImpl(String _name, Type _type, String _scope) {
		name = _name;
		type = _type;
		scope = _scope;
	}
	  
	protected static IRVarImpl create(String _name, Type _type, String _scope) {
		return new IRVarImpl(_name, _type, _scope);
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
	public String getScope() {
		return scope;
	}

	@Override
  public boolean isNullLoc() {
		return false;
  }
	
  @Override
  public boolean equals(Object o) {
    if(!(o instanceof IRVarImpl)) return false;
    IRVarImpl var = (IRVarImpl) o;
    return name.equals(var.getName()) && type == var.getType() && scope.equals(var.getScope());
  }
	
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append(name);
    if(scope != null) 
      sb.append(scope);
    if(type != null)
      sb.append("(type ").append(type.getName()).append(") ");
    return sb.toString();
  }
  
  protected String toStringShort() {
    StringBuilder sb = new StringBuilder();
    return sb.append(name).toString();
  }
}
