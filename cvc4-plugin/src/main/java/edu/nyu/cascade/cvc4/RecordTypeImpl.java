package edu.nyu.cascade.cvc4;

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Record;
import edu.nyu.acsys.CVC4.pairStringType;
import edu.nyu.acsys.CVC4.vectorPairStringType;
import edu.nyu.acsys.CVC4.vectorType;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.Expression.Kind;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.Type;

final class RecordTypeImpl extends TypeImpl implements RecordType {
	static RecordTypeImpl create(ExpressionManagerImpl em, String tname, String elemName, Type elemType) {
    return new RecordTypeImpl(em, tname, Lists.newArrayList(elemName), Lists.newArrayList(elemType));
  }

	static RecordTypeImpl create(ExpressionManagerImpl em, String tname, Iterable<String> elemNames,
      Iterable<? extends Type> elemTypes) {
    return new RecordTypeImpl(em, tname, elemNames, elemTypes);
  }
  
	static RecordTypeImpl create(ExpressionManagerImpl em, String tname) {
    ImmutableList<String> elemNames = ImmutableList.of();
    ImmutableList<? extends Type> elemTypes = ImmutableList.of();
    return new RecordTypeImpl(em, tname, elemNames, elemTypes);
  }

	@Override
	RecordExpressionImpl createExpression(Expr res, Expression e, Kind kind,
			Iterable<ExpressionImpl> children) {
		Preconditions.checkArgument(e.isRecord());
		return RecordExpressionImpl.create(getExpressionManager(), 
				kind, res, e.getType().asRecord(), children);
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

  private RecordTypeImpl(ExpressionManagerImpl em, String tname, 
      Iterable<String> fields, Iterable<? extends Type> types) {
    super(em);
    Preconditions.checkArgument(Iterables.size(fields) == Iterables.size(types));
    this.elementTypes = ImmutableList.copyOf(types);
    this.elementNames = ImmutableList.copyOf(fields);
    this.typeName = tname;
    
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
	public List<String> getElementNames() {
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
  public RecordBoundVariableImpl boundVar(String name, boolean fresh) {
    return RecordBoundVariableImpl.create(getExpressionManager(), name, this, fresh);
  }
  
  @Override
  public RecordBoundVariableImpl boundExpression(String name, int index, boolean fresh) {
    return boundVar(name, fresh);
  }

  @Override
  public String toString() {
    return elementTypes.toString();
  }

  @Override
  public String getName() {
    return typeName;
  }
  
  @Override
  public Type select(String fieldName) {
    int index = elementNames.indexOf(fieldName);
    return elementTypes.get(index);
  }

  @Override
  public RecordExpression update(Expression record, String fieldName,
      Expression value) {
	  return RecordExpressionImpl.mkUpdate(getExpressionManager(), record, fieldName, value);
  }
}
