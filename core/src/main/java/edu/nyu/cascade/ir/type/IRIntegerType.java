package edu.nyu.cascade.ir.type;

import xtc.type.NumberT;
import xtc.type.Type;

public final class IRIntegerType extends IRType {
  private static IRIntegerType singleton = null;
  
  private final Type srcType;
  
  static IRIntegerType getInstance() {
  	if(singleton != null) return singleton;
  	
  	singleton = create(NumberT.INT);
  	return singleton;
  }
  
  static IRIntegerType create(Type srcType) {
  	return new IRIntegerType(srcType); 
  }
  
  public Type getSrcType() {
  	return srcType;
  }
  
  private IRIntegerType(Type srcType) {
  	this.srcType = srcType;
  }
  
  @Override
  public String toString() { return "int"; }

  @Override
  public Kind getKind() {
    return Kind.INTEGER;
  }

/*  @Override
  public Object variable(IExpressionFactory<?, ?, ?> exprFactory, String id,
      boolean fresh) throws ExpressionFactoryException {
    return exprFactory.integerVar(id, fresh);
  }

  @Override
  public IType<?> toType(IExpressionManager exprManager) {
    return exprManager.integerType();
  }*/
}
