package edu.nyu.cascade.ir.type;

import java.util.Map;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Maps;

public final class IRListType<T extends IRType> extends IRType {
  private static final Map<IRType, IRListType<? extends IRType>> singletonMap = Maps.newHashMap();
  
  @SuppressWarnings("unchecked")
  public static <T extends IRType> IRListType<T> getInstance(T type) {
    IRListType<T> listType = (IRListType<T>) singletonMap.get(type);
    if(listType != null)
      return listType;
    
    listType = new IRListType<T>(type);
    singletonMap.put(type, listType);
    return listType;
  }
  
  private T type;
  
  private IRListType(T type) {
    this.type = type;
  }
  
  @Override
  public Kind getKind() {
    return Kind.LIST;
  }

  @Override
  public ImmutableList<? extends IRType> getTypeArguments() {
    return ImmutableList.of(type);
  }

  @Override
  public String toString() { return "list<" + type + ">"; }
}
