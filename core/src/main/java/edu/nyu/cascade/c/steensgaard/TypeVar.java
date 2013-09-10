package edu.nyu.cascade.c.steensgaard;

import xtc.type.Type;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.c.alias.AliasVar;

public class TypeVar implements AliasVar {
  private final ECR ecr;
  private final String name;
  private final Type type;
  private final Scope scope;
  
  private TypeVar(String _name, Type _type, Scope _scope) {
    name = _name;
    type = _type;
    scope = _scope;
    ecr = ECR.create(this, ValueType.location(ECR.createBottom(), ECR.createBottom()));
  }
  
  protected static TypeVar create(String _name, Type _type, Scope _scope) {
    return new TypeVar(_name, _type, _scope);
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
  
  public Scope getScope() {
    return scope;
  }
  
  @Override
  public boolean equals(Object o) {
    if(!(o instanceof TypeVar)) return false;
    TypeVar var = (TypeVar) o;
    return name.equals(var.getName()) && type.equals(var.getType()) && scope.equals(var.getScope());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("(TypeVar (name ").append(name).append(") (scope ").append(scope.getQualifiedName())
      .append(") (type ").append(type.getName()).append(") )");
    return sb.toString();
  }
  
  public String toStringShort() {
    StringBuilder sb = new StringBuilder();
    return sb.append("(TypeVar (name ").append(name).append(')').toString();
  }
}
