package edu.nyu.cascade.c.pass.alias.steens;

class BottomType extends ValueType {

	ValueTypeKind getKind() {
		return ValueTypeKind.BOTTOM;
	}

	@Override
	public String toString() {
		return "BOT";
	}

	@Override
	public boolean equals(Object t) {
		if (!(t instanceof BottomType))
			return false;
		return true;
	}
}
