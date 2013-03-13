package edu.nyu.cascade.ir.type;

import java.util.Map;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Maps;

public final class IRAsyncChannelType<T extends IRType> extends IRType {

  private static final Map<IRType, IRAsyncChannelType<? extends IRType>> singletonMap = Maps.newHashMap();
  
  @SuppressWarnings("unchecked")
  public static <T extends IRType> IRAsyncChannelType<T> getInstance(T type) {
    IRAsyncChannelType<T> channelType = (IRAsyncChannelType<T>) singletonMap.get(type);
    if(channelType != null)
      return channelType;
    
    channelType = new IRAsyncChannelType<T>(type);
    singletonMap.put(type, channelType);
    return channelType;
  }
  
  private T type;
  
  private IRAsyncChannelType(T type) {
    this.type = type;
  }
  
  @Override
  public ImmutableList<? extends IRType> getTypeArguments() {
    return ImmutableList.of(type);
  }

  @Override
  public String toString() { return "async-channel<" + type + ">"; }

  @Override
  public Kind getKind() {
    return Kind.ASYNC_CHANNEL;
  }
}
