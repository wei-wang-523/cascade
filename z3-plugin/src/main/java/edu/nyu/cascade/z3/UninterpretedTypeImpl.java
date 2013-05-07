package edu.nyu.cascade.z3;

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
      TheoremProverImpl.debugCall("uninterpretedType");
      setZ3Type(exprManager.getTheoremProver().getZ3Context().MkUninterpretedSort(name));
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
  public VariableExpressionImpl boundVariable(String name, boolean fresh) {
    throw new UnsupportedOperationException("bound variable is not supported in z3.");
  }

  @Override
  public DomainType getDomainType() {
    return DomainType.UNINTERPRETED;
  }
}
