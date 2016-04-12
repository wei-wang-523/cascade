package edu.nyu.cascade.c.pass.alias.steenscfs;

import com.google.common.collect.RangeMap;

class StructType extends ValueType {

	private final RangeMap<Long, ECR> fieldMap;
	private final Size size;
	private Parent parent;
	private boolean op;
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("STRUCT (")
				.append(size).append(", ")
				.append(fieldMap).append(", ")
				.append(parent).append(')');
		
		return sb.toString();
	}
	
	@Override
	public boolean equals(Object o) {
		if(!(o instanceof StructType)) return false;
		StructType that = (StructType) o;
		if(!parent.equals(that.parent)) return false;
		if(!size.equals(that.size)) return false;
		if(!fieldMap.equals(that.fieldMap)) return false;
		return true;
	}

	StructType(RangeMap<Long, ECR> map, Size size, Parent parent, boolean op) {
		this.size = size;
		this.parent = parent;
		this.fieldMap = map;
		this.op = op;
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
	
	@Override
	boolean hasOpTag() {
		return op;
	}

	@Override
	void enableOpTag() {
		op = true;
	}
	
	RangeMap<Long, ECR> getFieldMap() {
		return fieldMap;
	}
	
}
