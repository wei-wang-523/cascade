package edu.nyu.cascade.util;

/** A "unit" type having exactly one value. */
public final class Unit {
	private static final Unit VALUE = new Unit();

	private Unit() {
	}

	public static Unit value() {
		return VALUE;
	}
}
