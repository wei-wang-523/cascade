package edu.nyu.cascade.c.preprocessor.steensfs;

class BlankType extends ValueType {
	
	private Parent parent;
	private Size size;
	
	BlankType(Size size, Parent parent) {
		this.size = size;
		this.parent = parent;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("BLANK (")
				.append(size)
				.append(", ")
				.append(parent)
				.append(')');
		return sb.toString();
	}
	
	@Override
	ValueTypeKind getKind() {
		return ValueTypeKind.BLANK;
	}
	
	@Override
	void setSize(Size size) {
		this.size = size;
	}
	
	@Override
	Size getSize() {
		return size;
	}
	
	@Override
	Parent getParent() {
		return parent;
	}
	
	@Override
	void setParent(Parent parent) {
		this.parent = parent;
	}
}
