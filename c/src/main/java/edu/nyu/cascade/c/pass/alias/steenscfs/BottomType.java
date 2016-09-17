package edu.nyu.cascade.c.pass.alias.steenscfs;

class BottomType extends ValueType {

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof BottomType))
			return false;
		return true;
	}

	@Override
	ValueTypeKind getKind() {
		return ValueTypeKind.BOTTOM;
	}

	@Override
	public String toString() {
		return new StringBuilder().append("(BOT)").toString();
	}

	@Override
	Size getSize() {
		return Size.getBot();
	}

	@Override
	Parent getParent() {
		return Parent.getBottom();
	}

	@Override
	void setParent(Parent parent) {
		throw new UnsupportedOperationException();
	}

	@Override
	void setSize(Size size) {
		throw new UnsupportedOperationException();
	}
	
	@Override
	void setSource() {
		throw new UnsupportedOperationException();
	}
	
	@Override
	boolean isSource() {
		return false;
	}
}
