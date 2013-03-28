package edu.nyu.cascade.cvc4;

public final class BoundVarTypeImpl extends TypeImpl {
  static BoundVarTypeImpl create(ExpressionManagerImpl em) {
    return new BoundVarTypeImpl(em);
  }
  
  protected BoundVarTypeImpl(ExpressionManagerImpl em) {
    //FIXME: how to create Bound Var Type in cvc4
    super(em);
  }

  @Override
  public DomainType getDomainType() {
    return DomainType.BOUND_VAR_TYPE;
  }

  @Override
  public String getName() {
    return toString();
  }

  @Override
  public VariableExpressionImpl variable(String name, boolean fresh) {
    throw new UnsupportedOperationException("No variable with BoundVarType");
  }

  @Override
  public BoundVariableExpressionImpl boundVariable(String name, boolean fresh) {
    throw new UnsupportedOperationException("No bound variable with BoundVarType");
  }
}