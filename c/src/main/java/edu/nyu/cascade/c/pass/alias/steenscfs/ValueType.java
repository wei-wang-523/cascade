package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.List;
import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.Range;
import edu.nyu.cascade.util.Pair;

abstract class ValueType {

	enum ValueTypeKind {
		BOTTOM, BLANK, SIMPLE, STRUCT, LAMBDA
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

	static SimpleType simple(ECR loc, ECR func, Size size, Parent parent) {
		return new SimpleType(loc, func, size, parent);
	}

	static SimpleType simple(Pair<ECR, ECR> pair, Size size, Parent parent) {
		return simple(pair.fst(), pair.snd(), size, parent);
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
