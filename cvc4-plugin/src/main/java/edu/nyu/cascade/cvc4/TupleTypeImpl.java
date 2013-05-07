package edu.nyu.cascade.cvc4;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.vectorType;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;

public final class TupleTypeImpl extends TypeImpl implements TupleType {
  static TupleTypeImpl create(ExpressionManagerImpl em, Type firstType,
      Type... otherTypes) {
    return new TupleTypeImpl(em, Lists.asList(firstType, otherTypes));
  }

  static TupleTypeImpl create(ExpressionManagerImpl em,
      Iterable<? extends Type> types) {
    return new TupleTypeImpl(em, types);
  }

  static TupleTypeImpl valueOf(ExpressionManagerImpl em, Type t) {
    if (t instanceof TupleTypeImpl) {
      return (TupleTypeImpl) t;
    } else {
      return create(em, ((TupleType) t).getElementTypes());
    }
  }

  private final ImmutableList<Type> elementTypes;

  private TupleTypeImpl(ExpressionManagerImpl em, Iterable<? extends Type> types) {
    super(em);

    this.elementTypes = ImmutableList.copyOf(types);
    vectorType cvc4Types = new vectorType();
    for (Type t : elementTypes) {
      cvc4Types.add(em.toCvc4Type(t));
    }

    try {
      setCVC4Type(em.getTheoremProver().getCvc4ExprManager().mkTupleType(
          cvc4Types));
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }

  @Override
  public ImmutableList<Type> getElementTypes() {
    return elementTypes;
  }

  @Override
  public int size() {
    return elementTypes.size();
  }

  @Override
  public DomainType getDomainType() {
    return DomainType.TUPLE;
  }

  @Override
  public TupleVariableImpl variable(String name, boolean fresh) {
    return TupleVariableImpl.create(getExpressionManager(), name, this, fresh);
  }
  
  @Override
  public TupleBoundVariableImpl boundVariable(String name, boolean fresh) {
    return TupleBoundVariableImpl.create(getExpressionManager(), name, this, fresh);
  }

  @Override
  public String toString() {
    return elementTypes.toString();
  }

  @Override
  public String getName() {
    return toString();
  }
}
