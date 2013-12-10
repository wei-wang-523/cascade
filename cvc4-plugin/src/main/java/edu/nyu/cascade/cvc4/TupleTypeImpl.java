package edu.nyu.cascade.cvc4;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.vectorType;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;

public final class TupleTypeImpl extends TypeImpl implements TupleType {
  static TupleTypeImpl create(ExpressionManagerImpl em, String tname, Type firstType,
      Type... otherTypes) {
    return new TupleTypeImpl(em, tname, Lists.asList(firstType, otherTypes));
  }

  static TupleTypeImpl create(ExpressionManagerImpl em, String tname, 
      Iterable<? extends Type> types) {
    return new TupleTypeImpl(em, tname, types);
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

  private TupleTypeImpl(ExpressionManagerImpl em, String tname, Iterable<? extends Type> types) {
    super(em);

    this.elementTypes = ImmutableList.copyOf(types);
    this.typeName = tname;
    
    StringBuilder sb = new StringBuilder();
    
    sb.append(typeName + " : TYPE = [");
    
    vectorType cvc4Types = new vectorType();
    for (Type t : elementTypes) {
      cvc4Types.add(em.toCvc4Type(t));
      sb.append(em.toCvc4Type(t)).append(',');
    }
    
    sb.replace(sb.lastIndexOf(","), sb.lastIndexOf(",")+1, "]");

    try {
      setCVC4Type(em.getTheoremProver().getCvc4ExprManager().mkTupleType(
          cvc4Types));
      if(IOUtils.debugEnabled())
        TheoremProverImpl.debugCommand(sb.toString());
      if(IOUtils.tpFileEnabled())
        TheoremProverImpl.tpFileCommand(sb.toString());
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
    return typeName;
  }

	@Override
  public Expression index(Expression tuple, int index) {
	  return TupleExpressionImpl.mkTupleIndex(getExpressionManager(), tuple, index);
  }

	@Override
  public TupleExpression update(Expression tuple, int index, Expression value) {
	  return TupleExpressionImpl.mkUpdate(getExpressionManager(), tuple, index, value);
  }
}
