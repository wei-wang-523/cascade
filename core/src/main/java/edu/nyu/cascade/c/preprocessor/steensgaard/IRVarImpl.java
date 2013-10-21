package edu.nyu.cascade.c.preprocessor.steensgaard;

import xtc.type.Type;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.util.Identifiers;

public class IRVarImpl implements IRVar {
  private final ECR ecr;
  private final String name;
  private final Type type;
  private final Scope scope;
  
  private IRVarImpl(String _name, Type _type, Scope _scope) {
    name = _name;
    type = _type;
    scope = _scope;
    ecr = ECR.create(this, ValueType.location(ECR.createBottom(), ECR.createBottom()));
  }
  
  protected static IRVarImpl create(String _name, Type _type, Scope _scope) {
    return new IRVarImpl(_name, _type, _scope);
  }
  
  protected static IRVarImpl createNullLoc() {
    return new IRVarImpl(Identifiers.NULL_LOC_NAME, null, null);
  }
  
  protected ECR getECR() {
    return (ECR) ecr.findRoot();
  }
  
  protected ECR getOriginalECR() {
    return ecr;
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
  public Scope getScope() {
  	return scope;
  }
  
  @Override
  public boolean isNullLoc() {
    return Identifiers.NULL_LOC_NAME.equals(name) && type == null && scope == null;
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
