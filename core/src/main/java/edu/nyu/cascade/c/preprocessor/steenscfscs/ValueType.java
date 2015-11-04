package edu.nyu.cascade.c.preprocessor.steenscfscs;

import java.util.List;
import com.google.common.base.Preconditions;
import com.google.common.collect.RangeMap;

import edu.nyu.cascade.util.Pair;

abstract class ValueType {
	
	enum ValueTypeKind {
		BOTTOM,
		BLANK,
		SIMPLE,
		STRUCT,
		LAMBDA
	}
	
	abstract ValueTypeKind getKind();
	
	/**
	 * Get the size (the cell size) of the value type
	 * @return
	 */
	abstract Size getSize();
	
	/**
	 * Set the parent of the value type
	 * @return
	 */
	abstract void setParent(Parent parent);
	
	abstract Parent getParent();
	
	abstract boolean hasOpTag();
	
	abstract void enableOpTag();
	
	static BottomType bottom() {
		return new BottomType();
	}
	
	static BlankType blank(Size size, Parent parent) {
		return new BlankType(size, parent, false);
	}
	
	static BlankType blank(Size size, Parent parent, boolean op) {
		return new BlankType(size, parent, op);
	}
	
	static StructType struct(Size size, Parent parent) {
		Preconditions.checkNotNull(size);
		RangeMap<Long, ECR> fieldMap = FieldRangeMap.create();
		return struct(fieldMap, size, parent, false);
	}
	
	static StructType struct(RangeMap<Long, ECR> fieldMap, 
			Size size, 
			Parent parent,
			boolean op) {
		Preconditions.checkNotNull(size);
		return new StructType(fieldMap, size, parent, op);
	}
	
	static SimpleType simple(ECR loc, ECR func, Size size, Parent parent) {
	  return new SimpleType(loc, func, size, parent, false);
  }
	
	static SimpleType simple(ECR loc, ECR func, Size size, Parent parent, boolean op) {
	  return new SimpleType(loc, func, size, parent, op);
  }
	
	static SimpleType simple(Pair<ECR, ECR> pair, Size size, Parent parent) {
	  return simple(pair.fst(), pair.snd(), size, parent);
  }
	
	static SimpleType simple(Pair<ECR, ECR> pair, Size size, Parent parent, boolean op) {
	  return simple(pair.fst(), pair.snd(), size, parent, op);
  }
	
  static ValueType lam(ECR ret, List<ECR> args, Parent parent) {
    return new LambdaType(ret, args, parent);
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
	
	boolean isLambda() {
		return getKind().equals(ValueTypeKind.LAMBDA);
	}
	
	LambdaType asLambda() {
		Preconditions.checkArgument(isLambda());
		return (LambdaType) this;
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
