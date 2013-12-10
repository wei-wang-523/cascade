package edu.nyu.cascade.ir.type;

import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Maps;

import edu.nyu.cascade.util.Pair;

public final class IRPointerType<T extends IRType, S extends IRType> extends IRType {
  private static final Map<Pair<? extends IRType, ? extends IRType>, 
  	IRPointerType<? extends IRType, ? extends IRType>> singletonMap = Maps.newHashMap();
  
  @SuppressWarnings("unchecked")
  public static <T extends IRType, S extends IRType> IRPointerType<T, S> getInstance(T baseType, S offsetType) {
    IRPointerType<T, S> pointerType = (IRPointerType<T, S>) singletonMap.get(Pair.of(baseType, offsetType));
    if(pointerType != null)
      return pointerType;
    
    pointerType = new IRPointerType<T, S>(baseType, offsetType);
    singletonMap.put(Pair.of(baseType, offsetType), pointerType);
    return pointerType;
  }
  
  public static IRPointerType<?, ?> valueOf(IRType t) {
    Preconditions.checkArgument(Kind.POINTER.equals(t.getKind()));
    ImmutableList<? extends IRType> args = t.getTypeArguments();
    if( args.size() != 2 ) {
      throw new IllegalArgumentException("IRPointerType.valueOf: " + t);
    }
    return getInstance(args.get(0), args.get(1));
  }
  
  private final T baseType;
  private final S offsetType;
  
  private IRPointerType(T baseType, S offsetType) {
    this.baseType = baseType;
    this.offsetType = offsetType;
  }

  public T getbaseType() {
    return baseType;
  }

  public S getOffsetType() {
    return offsetType;
  }

  @Override
  public Kind getKind() {
    return Kind.POINTER;
  }

  @Override
  public ImmutableList<? extends IRType> getTypeArguments() {
    return ImmutableList.of(baseType,offsetType);
  }

  @Override
  public String toString() { return "pointer of (" + baseType + ", " + offsetType + ")"; }
}
