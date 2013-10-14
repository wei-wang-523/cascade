package edu.nyu.cascade.c.preprocessor.steensgaard;

import xtc.type.Type;
import edu.nyu.cascade.c.preprocessor.IREquivalentVar;
import edu.nyu.cascade.util.Identifiers;

public class TypeVar implements IREquivalentVar {
  private final ECR ecr;
  private final String name;
  private final Type type;
  private final String scope;
  
  private TypeVar(String _name, Type _type, String _scope) {
    name = _name;
    type = _type;
    scope = _scope;
    ecr = ECR.create(this, ValueType.location(ECR.createBottom(), ECR.createBottom()));
  }
  
  protected static TypeVar create(String _name, Type _type, String _scope) {
    return new TypeVar(_name, _type, _scope);
  }
  
  protected static TypeVar createNullLoc() {
    return new TypeVar(Identifiers.NULL_LOC_NAME, null, null);
  }
  
  protected ECR getECR() {
    return (ECR) ecr.findRoot();
  }
  
  protected ECR getOriginalECR() {
    return ecr;
  }
  
  public String getName() {
    return name;
  }
  
  public Type getType() {
    return type;
  }
  
  public String getScope() {
    return scope;
  }
  
  public boolean isNullLoc() {
    return Identifiers.NULL_LOC_NAME.equals(name) && type == null && scope == null;
  }
  
  @Override
  public boolean equals(Object o) {
    if(!(o instanceof TypeVar)) return false;
    TypeVar var = (TypeVar) o;
    return name.equals(var.getName()) && type == var.getType() && scope.equals(var.getScope());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("(TypeVar (name ").append(name).append(") ");
    if(scope != null) 
      sb.append("(scope ").append(scope)
      .append(") ");
    if(type != null)
      sb.append("(type ").append(type.getName()).append(") ");
    sb.append(")");
    return sb.toString();
  }
  
  protected String toStringShort() {
    StringBuilder sb = new StringBuilder();
    return sb.append("(TypeVar (name ").append(name).append(')').toString();
  }
}
