package edu.nyu.cascade.cvc4;

import java.util.List;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.inject.internal.Preconditions;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Record;
import edu.nyu.acsys.CVC4.pairStringType;
import edu.nyu.acsys.CVC4.vectorPairStringType;
import edu.nyu.acsys.CVC4.vectorType;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.Type;

public final class RecordTypeImpl extends TypeImpl implements RecordType {
  static RecordTypeImpl create(ExpressionManagerImpl em, String tname, String elemName, Type elemType) {
    return new RecordTypeImpl(em, tname, Lists.newArrayList(elemName), Lists.newArrayList(elemType));
  }

  static RecordTypeImpl create(ExpressionManagerImpl em, String tname, Iterable<String> elemNames,
      Iterable<? extends Type> elemTypes) {
    return new RecordTypeImpl(em, tname, elemNames, elemTypes);
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

  private RecordTypeImpl(ExpressionManagerImpl em, String tname, 
      Iterable<String> fields, Iterable<? extends Type> types) {
    super(em);
    Preconditions.checkArgument(Iterables.size(fields) == Iterables.size(types));
    this.elementTypes = ImmutableList.copyOf(types);
    this.elementNames = ImmutableList.copyOf(fields);
    
    vectorType cvc4Types = new vectorType();
    for (Type t : elementTypes) {
      cvc4Types.add(em.toCvc4Type(t));
    }

    try {
      vectorPairStringType vectorPair = new vectorPairStringType();
      for(int i = 0; i<Iterables.size(fields); i++) {
        pairStringType pair = new pairStringType();
        pair.setFirst(Iterables.get(fields, i));
        pair.setSecond(em.toCvc4Type(Iterables.get(types, i)));
        vectorPair.add(pair);
      }
      Record record = new Record(vectorPair);
      setCVC4Type(em.getTheoremProver().getCvc4ExprManager().mkRecordType(record));
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
  public RecordVariableImpl variable(String name, boolean fresh) {
    return RecordVariableImpl.create(getExpressionManager(), name, this, fresh);
  }
  
  @Override
  public RecordBoundVariableImpl boundVariable(String name, boolean fresh) {
    return RecordBoundVariableImpl.create(getExpressionManager(), name, this, fresh);
  }

  @Override
  public String toString() {
    return elementTypes.toString();
  }

  @Override
  public String getName() {
    return toString();
  }
  
  @Override
  public Type select(String fieldName) {
    int index = elementNames.indexOf(fieldName);
    return elementTypes.get(index);
  }

  @Override
  public List<String> getElementNames() {
    return elementNames;
  }

}
