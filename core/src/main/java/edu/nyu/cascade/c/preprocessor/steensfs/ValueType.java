package edu.nyu.cascade.c.preprocessor.steensfs;

import java.util.List;
import com.google.common.base.Preconditions;
import com.google.common.collect.RangeMap;

import edu.nyu.cascade.util.FieldRangeMap;
import edu.nyu.cascade.util.Pair;

abstract class ValueType {
	
	enum ValueTypeKind {
		BOTTOM,
		BLANK,
		SIMPLE,
		STRUCT,
		OBJECT, 
		LAMBDA
	}
	
	abstract ValueTypeKind getKind();
	
	/**
	 * Set the parent of the value type
	 * @return
	 */
	abstract void setParent(Parent parent);
	
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
	
	static BottomType bottom() {
		return new BottomType();
	}
	
	static BlankType blank(Size size, Parent parent) {
		return new BlankType(size, parent);
	}
	
	static ObjectType object(ECR loc, ECR func, Size size, Parent parent) {
		Preconditions.checkNotNull(loc.getOffset());
		return new ObjectType(loc, func, size, parent);
  }
	
	static ObjectType object(Pair<ECR, ECR> pair, Size size, Parent parent) {
	  return object(pair.fst(), pair.snd(), size, parent);
  }
	
	static StructType struct(Size size, Parent parent) {
		Preconditions.checkNotNull(size);
		RangeMap<Long, ECR> fieldMap = FieldRangeMap.create();
		return struct(fieldMap, size, parent);
	}
	
	static StructType struct(RangeMap<Long, ECR> fieldMap, 
			Size size, 
			Parent parent) {
		Preconditions.checkNotNull(size);
		return new StructType(fieldMap, size, parent);
	}
	
	static SimpleType simple(ECR loc, ECR func, Size size, Parent parent) {
		Preconditions.checkNotNull(loc.getOffset());
	  return new SimpleType(loc, func, size, parent);
  }
	
	static SimpleType simple(Pair<ECR, ECR> pair, Size size, Parent parent) {
	  return simple(pair.fst(), pair.snd(), size, parent);
  }
	
  static ValueType lam(ECR ret, 
  		List<ECR> args, 
  		Size size, 
  		Parent parent) {
    return new LambdaType(ret, args, size, parent);
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
	
	boolean isLambda() {
		return getKind().equals(ValueTypeKind.LAMBDA);
	}
	
	LambdaType asLambda() {
		Preconditions.checkArgument(isLambda());
		return (LambdaType) this;
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
