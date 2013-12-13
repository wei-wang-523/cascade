package edu.nyu.cascade.cvc4;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.Expression.Kind;

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

	@Override
	ExpressionImpl create(Expr res, Expression e, Kind subst,
			Iterable<ExpressionImpl> importExpressions) {
		throw new UnsupportedOperationException("No variable can be created via variable type");
	}
}