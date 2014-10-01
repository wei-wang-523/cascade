package edu.nyu.cascade.ir.type;

import java.util.Map;

import com.google.common.collect.Maps;

public final class IRChannelType<T extends IRType> extends IRType {
  private static final Map<IRType, IRChannelType<? extends IRType>> singletonMap = Maps.newHashMap();
  
  @SuppressWarnings("unchecked")
  public static <T extends IRType> IRChannelType<T> getInstance(T type) {
    IRChannelType<T> channelType = (IRChannelType<T>) singletonMap.get(type);
    if(channelType != null)
      return channelType;
    
    channelType = new IRChannelType<T>(type);
    singletonMap.put(type, channelType);
    return channelType;
  }
  
  private T type;
  
  private IRChannelType(T type) {
    this.type = type;
  }
  
  @Override
  public Kind getKind() {
    return Kind.CHANNEL;
  }

  @Override
  public String toString() { return "channel<" + type + ">"; }
}
