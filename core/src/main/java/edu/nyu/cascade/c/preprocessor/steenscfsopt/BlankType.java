package edu.nyu.cascade.c.preprocessor.steenscfsopt;

class BlankType extends ValueType {
	
	private Parent parent;
	private final Size size;
	private boolean op;
	
	BlankType(Size size, Parent parent, boolean op) {
		this.size = size;
		this.parent = parent;
		this.op = op;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("BLANK (")
				.append(size)
				.append(", ")
				.append(parent)
				.append(", ")
				.append(op)
				.append(')');
		return sb.toString();
	}
	
	@Override
	public boolean equals(Object o) {
		if(!(o instanceof BlankType)) return false;
		BlankType that = (BlankType) o;
		if(!size.equals(that.size)) return false;
		if(!parent.equals(that.parent))	return false;
		if(op != that.op) return false;
		return true;
	}

	/**
	 * Get Blank(T, {})
	 * @return
	 */
	static BlankType getTop() {
		return new BlankType(
				Size.getTop(), 
				Parent.getBottom(),
				false);
	}
	
	@Override
	ValueTypeKind getKind() {
		return ValueTypeKind.BLANK;
	}
	
	@Override
	void setParent(Parent parent) {
		this.parent = parent;
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
	boolean hasOpTag() {
		return op;
	}

	@Override
	void enableOpTag() {
		op = true;
	}
}
