package edu.nyu.cascade.util;

public interface ConversionStrategy<Left, Right> {
  Left rightToLeft(Right r) throws ConversionException;
  Right leftToRight(Left l) throws ConversionException;
}
