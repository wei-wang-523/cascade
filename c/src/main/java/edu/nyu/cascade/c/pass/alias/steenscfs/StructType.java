package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.Map;
import com.google.common.collect.Maps;
import com.google.common.collect.Range;

class StructType extends ValueType {

	private final Map<Range<Long>, ECR> _fieldMap;
	private Size _size;
	private Parent _parent;

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("STRUCT (").append(_size)
				.append(", ").append(_fieldMap).append(", ").append(_parent)
				.append(')');

		return sb.toString();
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof StructType))
			return false;
		StructType that = (StructType) o;
		if (!_parent.equals(that._parent))
			return false;
		if (!_size.equals(that._size))
			return false;
		if (!Maps.difference(_fieldMap, that._fieldMap).areEqual())
			return false;
		return true;
	}

	StructType(Map<Range<Long>, ECR> fieldMap, Size size, Parent parent) {
		_size = size;
		_parent = parent;
		_fieldMap = Maps.newHashMap(fieldMap);
	}

	ECR addFieldECR(Range<Long> range, ECR ecr) {
		if (_fieldMap.containsKey(range)) {
			return _fieldMap.get(range);
		} else {
			_fieldMap.put(range, ecr);
			return ecr;
		}
	}

	StructType(Size size, Parent parent) {
		_size = size;
		_parent = parent;
		_fieldMap = Maps.newHashMap();
	}

	@Override
	ValueTypeKind getKind() {
		return ValueTypeKind.STRUCT;
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
	void setParent(Parent parent) {
		_parent = parent;
	}

	Map<Range<Long>, ECR> getFieldMap() {
		return _fieldMap;
	}
}
