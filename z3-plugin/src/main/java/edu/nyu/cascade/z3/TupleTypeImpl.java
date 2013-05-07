package edu.nyu.cascade.z3;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;

public final class TupleTypeImpl extends TypeImpl implements TupleType {
  static TupleTypeImpl create(ExpressionManagerImpl em, String name, Type firstType,
      Type... otherTypes) {
    return new TupleTypeImpl(em, name, Lists.asList(firstType, otherTypes));
  }

  static TupleTypeImpl create(ExpressionManagerImpl em, String name,
      Iterable<? extends Type> types) {
    return new TupleTypeImpl(em, name, types);
  }

  static TupleTypeImpl valueOf(ExpressionManagerImpl em, Type t) {
    if (t instanceof TupleTypeImpl) {
      return (TupleTypeImpl) t;
    } else {
      return create(em, ((TupleType) t).getName(), ((TupleType) t).getElementTypes());
    }
  }

  private final ImmutableList<Type> elementTypes;
  private final String typeName;

  private TupleTypeImpl(ExpressionManagerImpl em, String name, Iterable<? extends Type> types) {
    super(em);
    this.elementTypes = ImmutableList.copyOf(types);
    this.typeName = name;
    try {
      Context z3_context = em.getTheoremProver().getZ3Context();
      Symbol tname = z3_context.MkSymbol(name);
      Sort[] z3Types = new Sort[Iterables.size(types)];
      Symbol[] symbols = new Symbol[Iterables.size(types)];
      for (int i = 0; i < Iterables.size(types); i++) {
        z3Types[i] = em.toZ3Type(Iterables.get(types, i));
        symbols[i] = z3_context.MkSymbol(i);
      }
      setZ3Type(z3_context.MkTupleSort(tname, symbols, z3Types));
    } catch (Z3Exception e) {
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
  public String toString() {
    return new StringBuilder().append(typeName).append('(')
        .append(elementTypes).append(')').toString();
  }

  @Override
  public String getName() {
    return typeName;
  }

  @Override
  public VariableExpressionImpl boundVariable(String name, boolean fresh) {
    throw new UnsupportedOperationException("bound variable is not supported in z3.");
  }

}
