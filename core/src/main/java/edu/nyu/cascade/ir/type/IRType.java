package edu.nyu.cascade.ir.type;

import com.google.common.collect.ImmutableList;


public abstract class IRType {
  public static enum Kind {
    ARRAY, 
    ASYNC_CHANNEL, 
    BOOLEAN, 
    CHANNEL, 
    INTEGER, 
    LIST, 
    PROCESS, 
    RANGE,
    POINTER;
  }
  
  public abstract Kind getKind();

  public ImmutableList<? extends IRType> getTypeArguments() {
    return ImmutableList.of();
  }
  
  /*Object variable(IExpressionFactory<?, ?, ?> exprFactory, String id,
      boolean fresh) throws ExpressionFactoryException;
  IType<?> toType(IExpressionManager exprManager) ;*/
}
