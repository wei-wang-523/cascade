package edu.nyu.cascade.ir.type;

import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Maps;

import edu.nyu.cascade.util.Pair;

public final class IRArrayType<T extends IRType> extends IRType {
  private static final Map<Pair<IRType, ? extends IRType>, IRArrayType<? extends IRType>> singletonMap = Maps.newHashMap();
  
  @SuppressWarnings("unchecked")
  public static <T extends IRType> IRArrayType<T> getInstance(IRType range, T type) {
    IRArrayType<T> arrayType = (IRArrayType<T>) singletonMap.get(Pair.of(range, type));
    if(arrayType != null)
      return arrayType;
    
    arrayType = new IRArrayType<T>(range, type);
    singletonMap.put(Pair.of(range, type), arrayType);
    return arrayType;
  }
  
  @SuppressWarnings("unchecked")
  public static IRArrayType<?> valueOf(IRType t) {
    Preconditions.checkArgument(Kind.ARRAY.equals(t.getKind()));
    IRArrayType<? extends IRType> arrayType = (IRArrayType<? extends IRType>) t;
    ImmutableList<IRType> args = ImmutableList.of(arrayType.indexType, arrayType.elementType);
    if( args.size() != 2 || !(args.get(0) instanceof IRRangeType)) {
      throw new IllegalArgumentException("IRArrayType.valueOf: " + t);
    }
    return getInstance((IRRangeType<?>)args.get(0),args.get(1));
  }
  
  private final IRType indexType;
  private final T elementType;
  
  private IRArrayType(IRType range, T rangeType) {
    this.indexType = range;
    this.elementType = rangeType;
  }

  public IRType getIndexType() {
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
  public String toString() { return "array " + indexType + " of " + elementType; }
}
