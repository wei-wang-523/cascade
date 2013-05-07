package edu.nyu.cascade.cvc4;

import com.google.common.base.Preconditions;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.prover.type.UninterpretedType;

public final class UninterpretedTypeImpl extends TypeImpl implements UninterpretedType {
  private final String name;

  static UninterpretedTypeImpl create(
      ExpressionManagerImpl exprManager, String name) {
    return new UninterpretedTypeImpl(exprManager, name);
  }
  
  static UninterpretedTypeImpl valueOf(
      ExpressionManagerImpl exprManager, Type type) {
    Preconditions.checkArgument(type.isUninterpreted());
    if (type instanceof UninterpretedTypeImpl) {
      return (UninterpretedTypeImpl) type;
    } else {
      UninterpretedType uninterType = type.asUninterpreted();
      return create(exprManager, uninterType.getName());
    }
  }

  private UninterpretedTypeImpl(ExpressionManagerImpl exprManager, String name) {
    super(exprManager);
    this.name = name;
    try {
      TheoremProverImpl.debugCall("uninterpretedType of " + name);
      setCVC4Type(exprManager.getTheoremProver().getCvc4ExprManager().mkSort(name));
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }

  @Override
  public UninterpretedVariableImpl variable(String name, boolean fresh) {
    return UninterpretedVariableImpl.create(getExpressionManager(),name,this,fresh);
  }

  @Override
  public String toString() {
    return "UNINTERPRETED " + " OF "+ name ;
  }

  @Override
  public String getName() {
    return toString();
  }

  @Override
  public DomainType getDomainType() {
    return DomainType.UNINTERPRETED;
  }

  @Override
  public BoundVariableExpressionImpl boundVariable(String name, boolean fresh) {
    // TODO Auto-generated method stub
    return null;
  }
}
