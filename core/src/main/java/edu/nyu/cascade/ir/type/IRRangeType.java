package edu.nyu.cascade.ir.type;


public final class IRRangeType<T> extends IRType {
  public static <T> IRRangeType<T> create(Class<T> boundType, T lowerBound,
      T upperBound) {
    return new IRRangeType<T>(boundType, lowerBound, upperBound);
  }
  
  private final Class<T> boundType;
  private final T lowerBound, upperBound;

  private IRRangeType(Class<T> boundType, T lowerBound, T upperBound) {
//    Preconditions.checkArgument(lowerBound.getType().equals(upperBound.getType()));
    this.boundType = boundType;
    this.lowerBound = lowerBound;
    this.upperBound = upperBound;
  }

  @Override
  public Kind getKind() {
    return Kind.RANGE;
  }

  public T getLowerBound() {
    return lowerBound;
  }

  public T getUpperBound() {
    return upperBound;
  }
  
  @Override
  public String toString() {
    return "[" + lowerBound + ".." + (upperBound!=null?upperBound:"") + "]";
  }

  public Class<T> getBoundType() {
    return boundType;
  }
  
/*  public static IRRangeType valueOf(IRType t) {
    Preconditions.checkArgument(Kind.RANGE.equals(t.getKind()));
    ImmutableList<? extends IRType> args = t.getTypeArguments();
    if (args.size() != 2 || !(args.get(0) instanceof IRRangeType)) {
      throw new IllegalArgumentException("IRArrayType.valueOf: " + t);
    }
    return getInstance((IRRangeType) args.get(0), args.get(1));
  }*/

}
