package edu.nyu.cascade.c.pass.alias.steenscfs;

class BlankType extends ValueType {

	private Parent parent;
	private final Size size;

	BlankType(Size size, Parent parent) {
		this.size = size;
		this.parent = parent;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("BLANK (").append(size)
				.append(", ").append(parent).append(')');
		return sb.toString();
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof BlankType))
			return false;
		BlankType that = (BlankType) o;
		if (!size.equals(that.size))
			return false;
		if (!parent.equals(that.parent))
			return false;
		return true;
	}

	/**
	 * Get Blank(T, {})
	 * 
	 * @return
	 */
	static BlankType getTop() {
		return new BlankType(Size.getTop(), Parent.getBottom());
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
}
