package edu.nyu.cascade.c.pass.alias.steenscfs;

class BlankType extends ValueType {

	private Parent _parent;
	private Size _size;
	private boolean _isSource = false;

	BlankType(Size size, Parent parent) {
		_size = size;
		_parent = parent;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("BLANK (").append(_size)
				.append(", ").append(_parent).append(')');
		if (_isSource) sb.append(": ").append("source");
		return sb.toString();
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof BlankType))
			return false;
		BlankType that = (BlankType) o;
		if (!_size.equals(that._size))
			return false;
		if (!_parent.equals(that._parent))
			return false;
		if (_isSource != that._isSource )
			return false;
		return true;
	}

	@Override
	ValueTypeKind getKind() {
		return ValueTypeKind.BLANK;
	}

	@Override
	void setParent(Parent parent) {
		_parent = parent;
	}

	@Override
	void setSize(Size size) {
		_size = size;
	}

	@Override
	Size getSize() {
		return _size;
	}

	@Override
	Parent getParent() {
		return _parent;
	}
	
	@Override
	void setSource() {
		_isSource = true;
	}
	
	@Override
	boolean isSource() {
		return _isSource;
	}
}
