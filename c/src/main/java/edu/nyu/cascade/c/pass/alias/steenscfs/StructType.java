package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.Map;
import com.google.common.collect.Maps;
import com.google.common.collect.Range;

class StructType extends ValueType {

	private final Map<Range<Long>, ECR> fieldMap_;
	private final Size size;
	private Parent parent;

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("STRUCT (").append(size)
				.append(", ").append(fieldMap_).append(", ").append(parent).append(')');

		return sb.toString();
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof StructType))
			return false;
		StructType that = (StructType) o;
		if (!parent.equals(that.parent))
			return false;
		if (!size.equals(that.size))
			return false;
		if (!fieldMap_.equals(that.fieldMap_))
			return false;
		return true;
	}

	StructType(Map<Range<Long>, ECR> fieldMap, Size size, Parent parent) {
		this.size = size;
		this.parent = parent;
		fieldMap_ = Maps.newHashMap(fieldMap);
	}

	ECR addFieldECR(Range<Long> range, ECR ecr) {
		if (fieldMap_.containsKey(range)) {
			return fieldMap_.get(range);
		} else {
			fieldMap_.put(range, ecr);
			return ecr;
		}
	}

	StructType(Size size, Parent parent) {
		this.size = size;
		this.parent = parent;
		fieldMap_ = Maps.newHashMap();
	}

	@Override
	ValueTypeKind getKind() {
		return ValueTypeKind.STRUCT;
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

	Map<Range<Long>, ECR> getFieldMap() {
		return fieldMap_;
	}
}
