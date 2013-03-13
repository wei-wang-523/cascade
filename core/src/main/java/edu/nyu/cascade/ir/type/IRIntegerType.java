package edu.nyu.cascade.ir.type;

public final class IRIntegerType extends IRType {
  private static final IRIntegerType singleton = new IRIntegerType();
  
  public static IRIntegerType getInstance() {
    return singleton; 
  }
  
  private IRIntegerType() { 
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
