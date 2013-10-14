package edu.nyu.cascade.ir.expr;

import xtc.tree.Node;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

public interface IRSingleHeapEncoder {
	
	ArrayType getSizeArrType();
	
	ArrayType getMemoryType();
	
	Type getAddressType();
	
	Type getValueType();

	Expression freshAddress(String varName, IRVarInfo info, xtc.type.Type type);
	
	Expression freshRegion(String regionName, Node regionNode);
	
	ArrayExpression updateSizeArr(ArrayExpression sizeArr, Expression lval, Expression rval);
	
	ArrayExpression updateMemArr(ArrayExpression memArr, Expression lval, Expression rval);
	
	Expression getConstSizeArr(ArrayType sizeArrType);
	
	Expression getValueZero();
	
	Expression getUnknownValue(xtc.type.Type type);
	
	Expression getNullAddress();
	
	ImmutableSet<BooleanExpression> disjointMemLayout(
			ArrayExpression sizeArr);
	
	BooleanExpression validMalloc(
			ArrayExpression sizeArr, Expression ptr, Expression size);	

	BooleanExpression validFree(
			ArrayExpression sizeArr, Expression ptr);
	
	ImmutableSet<BooleanExpression> validMemAccess(
			ArrayExpression sizeArr, Expression ptr);
	
	ImmutableSet<BooleanExpression> validMemAccess(
			ArrayExpression sizeArr, Expression ptr, Expression size);

	Expression indexMemArr(ArrayExpression memArr, Expression p);

	Expression addressOf(Expression content);
}
