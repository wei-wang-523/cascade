package edu.nyu.cascade.ir.type;

public final class IRBooleanType extends IRType {
  private static final IRBooleanType singleton = new IRBooleanType();
  
  public static IRBooleanType getInstance() {
    return singleton; 
  }
  
  private IRBooleanType() { }
  
  @Override
  public String toString() { return "boolean"; }

  @Override
  public Kind getKind() {
    return Kind.BOOLEAN;
  }

}
