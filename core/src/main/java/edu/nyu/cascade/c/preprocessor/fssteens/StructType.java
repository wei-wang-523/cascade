package edu.nyu.cascade.c.preprocessor.fssteens;

import java.util.Map;

import xtc.type.Type;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

public class StructType extends ValueType {

	private final Parent parent;
	private final Map<Long, ECR> mapping;
	private final Type xtcType;
	private final String scopeName;
	private ECR address;
	private Size size;
	
	@Override
  ValueTypeKind getKind() {
	  return ValueTypeKind.STRUCT;
  }
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("STRUCT (")
				.append(size).append(", ")
				.append(mapping).append(", ")
				.append(parent).append(')');
		
		return sb.toString();
	}

	StructType(Map<Long, ECR> map, Size size, Parent parent, Type xtcType, String scopeName) {
		this.size = size;
		this.parent = parent;
		this.mapping = map;
		this.xtcType = xtcType;
		this.scopeName = scopeName;
	}
	
	StructType(Size size, Parent parent, Type xtcType, String scopeName) {
		this.size = size;
		this.parent = parent;
		this.mapping = Maps.newTreeMap();
		this.xtcType = xtcType;
		this.scopeName = scopeName;
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
	String getScopeName() {
		return scopeName;
	}
	
	@Override
	Type getXtcType() {
		return xtcType;
	}
	
	@Override
	void setAddress(ECR address) {
		Preconditions.checkArgument(this.address == null);
		this.address = address;
	}
	
	@Override
	ECR getAddress() {
		return address;
	}

	Map<Long, ECR> getMapping() {
		return mapping;
	}
	
}
