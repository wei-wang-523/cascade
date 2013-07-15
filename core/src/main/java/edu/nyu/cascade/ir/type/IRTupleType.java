package edu.nyu.cascade.ir.type;

import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Maps;

import edu.nyu.cascade.util.Pair;

public final class IRTupleType<T extends IRType> extends IRType {
  private static final Map<Pair<? extends IRType, ? extends IRType>, IRTupleType<? extends IRType>> singletonMap = Maps.newHashMap();
  
  @SuppressWarnings("unchecked")
  public static <T extends IRType> IRTupleType<T> getInstance(T refType, T offsetType) {
    IRTupleType<T> pointerType = (IRTupleType<T>) singletonMap.get(Pair.of(refType, offsetType));
    if(pointerType != null)
      return pointerType;
    
    pointerType = new IRTupleType<T>(refType, offsetType);
    singletonMap.put(Pair.of(refType, offsetType), pointerType);
    return pointerType;
  }
  
  public static IRTupleType<?> valueOf(IRType t) {
    Preconditions.checkArgument(Kind.TUPLE.equals(t.getKind()));
    ImmutableList<? extends IRType> args = t.getTypeArguments();
    if( args.size() != 2 ) {
      throw new IllegalArgumentException("IRTupleType.valueOf: " + t);
    }
    return getInstance(args.get(0), args.get(1));
  }
  
  private final T refType;
  private final T offsetType;
  
  private IRTupleType(T refType, T offsetType) {
    this.refType = refType;
    this.offsetType = offsetType;
  }

  public T getRefType() {
    return refType;
  }

  public T getOffsetType() {
    return offsetType;
  }

  @Override
  public Kind getKind() {
    return Kind.TUPLE;
  }

  @Override
  public ImmutableList<T> getTypeArguments() {
    return ImmutableList.of(refType,offsetType);
  }

  @Override
  public String toString() { return "pointer of (" + refType + ", " + offsetType + ")"; }
}
