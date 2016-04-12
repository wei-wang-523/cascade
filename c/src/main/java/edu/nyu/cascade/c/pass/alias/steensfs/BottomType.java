package edu.nyu.cascade.c.pass.alias.steensfs;

class BottomType extends ValueType {
	
	@Override
	ValueTypeKind getKind() {
		return ValueTypeKind.BOTTOM;
	}
	
	@Override
	public String toString() {
		return new StringBuilder().append("BOT").toString();
	}
	
	@Override
	void setSize(Size size) {
		throw new UnsupportedOperationException("Cannot set size for bottom type");
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
}
