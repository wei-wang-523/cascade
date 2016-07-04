package edu.nyu.cascade.ir.type;

public final class IRLabelType extends IRType {
  private static final IRLabelType singleton = new IRLabelType();
  
	public static IRLabelType getInstance() {
    return singleton; 
  }
  
  private IRLabelType() { 
  }
  
  @Override
  public String toString() { return "label"; }

  @Override
  public Kind getKind() {
    return Kind.LABEL;
  }

}
