package edu.nyu.cascade.util;

public final class ConvertibleValues {
  public static <Left, Right> ConvertibleValue<Left, Right> fromLeft(
      final ConversionStrategy<Left, Right> strategy, final Left a) {
    return new ConvertibleValue<Left, Right>() {
      @Override
      public Right right() throws ConversionException {
        return strategy.leftToRight(a);
      }

      @Override
      public Left left() {
        return a;
      }
      
      public String toString() {
        return "(ConvertibleValue left:" + a.toString() + ")";
      }
    };
  }

  public static <Left, Right> ConvertibleValue<Left, Right> fromRight(
      final ConversionStrategy<Left, Right> strategy, final Right b) {
    return new ConvertibleValue<Left, Right>() {

      @Override
      public Right right() {
        return b;
      }

      @Override
      public Left left() throws ConversionException {
        return strategy.rightToLeft(b);
      }
      
      public String toString() {
        return "(ConvertibleValue right:" + b.toString() + ")";
      }
    };
  }
}
