package edu.nyu.cascade.c.pass.alias.steensfs;

import com.google.common.collect.RangeMap;

class StructType extends ValueType {

	private final RangeMap<Long, ECR> fieldMap;
	private Parent parent;
	private Size size;
	
	@Override
  ValueTypeKind getKind() {
	  return ValueTypeKind.STRUCT;
  }
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("STRUCT (")
				.append(size).append(", ")
				.append(fieldMap).append(", ")
				.append(parent).append(')');
		
		return sb.toString();
	}

	StructType(RangeMap<Long, ECR> map, Size size, Parent parent) {
		this.size = size;
		this.parent = parent;
		this.fieldMap = map;
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
	
	RangeMap<Long, ECR> getFieldMap() {
		return fieldMap;
	}
	
}
