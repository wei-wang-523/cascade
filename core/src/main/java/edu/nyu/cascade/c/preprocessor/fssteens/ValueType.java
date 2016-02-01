package edu.nyu.cascade.c.preprocessor.fssteens;

import java.util.Map;

import com.google.common.base.Preconditions;

import xtc.type.Type;
import edu.nyu.cascade.util.Pair;

abstract class ValueType {
	
	enum ValueTypeKind {
		BOTTOM,
		BLANK,
		SIMPLE,
		STRUCT,
		OBJECT
	}
	
	abstract ValueTypeKind getKind();
	
	/**
	 * Get the size (the cell size) of the value type
	 * @return
	 */
	abstract Size getSize();
	
	/**
	 * Set the size (the cell size) of the value type
	 * @return
	 */
	abstract void setSize(Size size);
	
	abstract Parent getParent();
	
	boolean hasAddress() {
	  return getAddress() != null;
	}

	abstract void setAddress(ECR address);
	
	abstract ECR getAddress();
	
	abstract Type getXtcType();
	
	abstract String getScopeName();
	
	static BottomType bottom() {
		return new BottomType();
	}
	
	static BlankType blank(Size size, Parent parent, Type xtcType, String scopeName) {
		Preconditions.checkNotNull(size);
		Preconditions.checkNotNull(scopeName);
		return new BlankType(size, parent, xtcType, scopeName);
	}
	
	static ObjectType object(Pair<ECR, Offset> loc,
			Function func,
			Size size,
			Parent parent,
			Type xtcType,
			String scopeName) {
		Preconditions.checkNotNull(size);
		return new ObjectType(loc.fst(), loc.snd(), func, size, parent, xtcType, scopeName);
  }
	
	static StructType struct(Size size, 
			Parent parent,
			Type xtcType,
			String scopeName) {
		Preconditions.checkNotNull(size);
		Preconditions.checkNotNull(scopeName);
		return new StructType(size, parent, xtcType, scopeName);
	}
	
	static StructType struct(Map<Long, ECR> map, 
			Size size, 
			Parent parent,
			Type xtcType,
			String scopeName) {
		Preconditions.checkNotNull(size);
		Preconditions.checkNotNull(scopeName);
		return new StructType(map, size, parent, xtcType, scopeName);
	}
	
	static SimpleType simple(Pair<ECR, Offset> loc,
			Function func,
			Size size,
			Parent parent,
			Type xtcType,
			String scopeName) {
		Preconditions.checkNotNull(size);
		Preconditions.checkNotNull(scopeName);
	  return new SimpleType(loc.fst(), loc.snd(), func, size, parent, xtcType, scopeName);
  }
	
	boolean isBottom() {
		return getKind().equals(ValueTypeKind.BOTTOM);
	}
	
	boolean isBlank() {
		return getKind().equals(ValueTypeKind.BLANK);
	}
	
	boolean isSimple() {
		return getKind().equals(ValueTypeKind.SIMPLE);
	}
	
	boolean isObject() {
		return getKind().equals(ValueTypeKind.OBJECT);
	}
	
	boolean isStruct() {
		return getKind().equals(ValueTypeKind.STRUCT);
	}

	ObjectType asObject() {
	  Preconditions.checkArgument(isObject());
	  return (ObjectType) this;
  }
	
	SimpleType asSimple() {
		Preconditions.checkArgument(isSimple());
		return (SimpleType) this;
	}
	
	BottomType asBottom() {
		Preconditions.checkArgument(isBottom());
		return (BottomType) this;
	}
	
	BlankType asBlank() {
		Preconditions.checkArgument(isBlank());
		return (BlankType) this;
  }
	
	StructType asStruct() {
		Preconditions.checkArgument(isStruct());
		return (StructType) this;
	}
}
