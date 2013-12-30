package edu.nyu.cascade.ir.type;

import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Maps;

import edu.nyu.cascade.util.Pair;

public final class IRArrayType<T extends IRType> extends IRType {
  private static final Map<Pair<? extends IRRangeType<?>, ? extends IRType>, IRArrayType<? extends IRType>> singletonMap = Maps.newHashMap();
  
  @SuppressWarnings("unchecked")
  public static <T extends IRType> IRArrayType<T> getInstance(IRRangeType<?> range, T type) {
    IRArrayType<T> arrayType = (IRArrayType<T>) singletonMap.get(Pair.of(range, type));
    if(arrayType != null)
      return arrayType;
    
    arrayType = new IRArrayType<T>(range, type);
    singletonMap.put(Pair.of(range, type), arrayType);
    return arrayType;
  }
  
  public static IRArrayType<?> valueOf(IRType t) {
    Preconditions.checkArgument(Kind.ARRAY.equals(t.getKind()));
    ImmutableList<? extends IRType> args = t.getTypeArguments();
    if( args.size() != 2 || !(args.get(0) instanceof IRRangeType)) {
      throw new IllegalArgumentException("IRArrayType.valueOf: " + t);
    }
    return getInstance((IRRangeType<?>)args.get(0),args.get(1));
  }
  
  private final IRRangeType<?> indexType;
  private final T elementType;
  
  private IRArrayType(IRRangeType<?> indexType, T rangeType) {
    this.indexType = indexType;
    this.elementType = rangeType;
  }

  public IRRangeType<?> getIndexType() {
    return indexType;
  }

  public T getElementType() {
    return elementType;
  }

  @Override
  public Kind getKind() {
    return Kind.ARRAY;
  }

  @Override
  public ImmutableList<IRType> getTypeArguments() {
    return ImmutableList.of(indexType,elementType);
  }

  @Override
  public String toString() { return "array " + indexType + " of " + elementType; }

  /*  @Override
  public Object variable(IExpressionFactory<?, ?, ?> exprFactory, String id,
      boolean fresh) throws ExpressionFactoryException {
    IExpressionManager exprManager = exprFactory.getExpressionManager();
    try {
      return exprManager.arrayVar(id, range.toType(exprManager), type
          .toType(exprManager), fresh);
    } catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
  }

  @Override
  public IType<?> toType(IExpressionManager exprManager) {
    return exprManager.arrayType(range.toType(exprManager), type
        .toType(exprManager));
  }*/
}
