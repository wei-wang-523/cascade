package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.Range;

abstract class ValueType {

	enum ValueTypeKind {
		BOTTOM, BLANK, SIMPLE, STRUCT
	}

	abstract ValueTypeKind getKind();

	/**
	 * Get the size (the cell size) of the value type
	 * 
	 * @return
	 */
	abstract Size getSize();

	/**
	 * Set the parent of the value type
	 * 
	 * @return
	 */
	abstract void setParent(Parent parent);

	abstract void setSize(Size size);
	
	abstract void setSource();
	
	abstract boolean isSource();

	abstract Parent getParent();

	static BottomType bottom() {
		return new BottomType();
	}

	static BlankType blank(Size size, Parent parent) {
		return new BlankType(size, parent);
	}

	static StructType struct(Size size, Parent parent) {
		Preconditions.checkNotNull(size);
		return new StructType(size, parent);
	}

	static StructType struct(Map<Range<Long>, ECR> fieldMap, Size size,
			Parent parent) {
		Preconditions.checkNotNull(size);
		return new StructType(fieldMap, size, parent);
	}

	static SimpleType simple(ECR loc, Size size, Parent parent) {
		return new SimpleType(loc, size, parent);
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

	boolean isStruct() {
		return getKind().equals(ValueTypeKind.STRUCT);
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
