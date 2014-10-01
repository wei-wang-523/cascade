package edu.nyu.cascade.ir.type;

import xtc.type.Type;

public final class IRUnknownType extends IRType {
  private final Type xtcType;
  
  private IRUnknownType(Type xtcType) { 
  	this.xtcType = xtcType;
  }
  
  static IRUnknownType create(Type xtcType) {
  	return new IRUnknownType(xtcType);
  }
  
  public Type getXtcType() {
  	return xtcType;
  }
  
  @Override
  public String toString() { return xtcType.resolve().toString(); }

  @Override
  public Kind getKind() {
    return Kind.UNKNOWN;
  }

}
