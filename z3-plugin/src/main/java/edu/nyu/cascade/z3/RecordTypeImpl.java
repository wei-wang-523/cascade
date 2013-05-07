package edu.nyu.cascade.z3;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.microsoft.z3.Constructor;
import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.Type;

public final class RecordTypeImpl extends TypeImpl implements RecordType {
  static RecordTypeImpl create(ExpressionManagerImpl em, String name, 
      Iterable<String> elemNames, Iterable<? extends Type> elemTypes) {
    return new RecordTypeImpl(em, name, elemNames, elemTypes);
  }

  static RecordTypeImpl create(ExpressionManagerImpl em, String name, String elemName, Type elemType) {
    return new RecordTypeImpl(em, name, Lists.newArrayList(elemName), Lists.newArrayList(elemType));
  }

  static RecordTypeImpl valueOf(ExpressionManagerImpl em, Type t) {
    if (t instanceof RecordTypeImpl) {
      return (RecordTypeImpl) t;
    } else {
      return create(em, ((RecordType) t).getName(), 
          ((RecordType) t).getElementNames(), ((RecordType) t).getElementTypes());
    }
  }

  private final ImmutableList<Type> elementTypes;
  private final ImmutableList<String> elementNames;
  private final String typeName;

  private RecordTypeImpl(ExpressionManagerImpl em, String name, 
      Iterable<String> elemNames, Iterable<? extends Type> elemTypes) {
    super(em);
    this.elementTypes = ImmutableList.copyOf(elemTypes);
    this.typeName = name;
    this.elementNames = ImmutableList.copyOf(elemNames);
    try {
      Context z3_context = em.getTheoremProver().getZ3Context();
      Sort[] z3Types = new Sort[Iterables.size(elemTypes)];
      String[] symbols = Iterables.toArray(elemNames, String.class);
      int[] refs = new int[Iterables.size(elemTypes)];
      for (int i = 0; i < Iterables.size(elemTypes); i++) {
        z3Types[i] = em.toZ3Type(Iterables.get(elemTypes, i));
        refs[i] = 0;
      }
      Constructor[] cons = new Constructor[]{
          z3_context.MkConstructor(name, "is-" + name, symbols, z3Types, refs)};
      setZ3Type(z3_context.MkDatatypeSort(name, cons));
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
  }

  @Override
  public ImmutableList<Type> getElementTypes() {
    return elementTypes;
  }
  
  @Override
  public ImmutableList<String> getElementNames() {
    return elementNames;
  }

  @Override
  public int size() {
    return elementTypes.size();
  }

  @Override
  public DomainType getDomainType() {
    return DomainType.RECORD;
  }

  @Override
  public RecordVariableImpl variable(String name, boolean fresh) {
    return RecordVariableImpl.create(getExpressionManager(), name, this, fresh);
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

  @Override
  public Type select(String fieldName) {
    int i = elementNames.indexOf(fieldName);
    return elementTypes.get(i);
  }
}
