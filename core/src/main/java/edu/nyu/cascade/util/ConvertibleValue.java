package edu.nyu.cascade.util;

public interface ConvertibleValue<Left, Right> {
	Left left() throws ConversionException;

	Right right() throws ConversionException;
}
