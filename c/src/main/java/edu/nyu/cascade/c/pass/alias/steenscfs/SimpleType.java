package edu.nyu.cascade.c.pass.alias.steenscfs;

class SimpleType extends ValueType {

	private final ECR _loc;
	private Size _size;
	private Parent _parent;
	private boolean _isSource;

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("SIMPLE (")
				.append(((ECR) _loc.findRoot()).getId()).append(", ").append(_size)
				.append(", ").append(_parent).append(')');
		if (_isSource) sb.append(": ").append("source");
		return sb.toString();
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof SimpleType))
			return false;
		SimpleType that = (SimpleType) o;
		if (!_loc.equals(that._loc))
			return false;
		if (!_size.equals(that._size))
			return false;
		if (!_parent.equals(that._parent))
			return false;
		if (_isSource != that._isSource )
			return false;
		return true;
	}

	SimpleType(ECR loc, Size size, Parent parent) {
		_loc = loc;
		_size = size;
		_parent = parent;
	}

	@Override
	ValueTypeKind getKind() {
		return ValueTypeKind.SIMPLE;
	}

	@Override
	Size getSize() {
		return _size;
	}

	@Override
	void setSize(Size size) {
		_size = size;
	}

	@Override
	Parent getParent() {
		return _parent;
	}

	@Override
	void setParent(Parent parent) {
		_parent = parent;
	}
	
	@Override
	void setSource() {
		_isSource = true;
	}
	
	@Override
	boolean isSource() {
		return _isSource;
	}

	ECR getLoc() {
		return _loc;
	}
}
