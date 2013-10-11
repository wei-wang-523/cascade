package edu.nyu.cascade.ir.expr;

import xtc.tree.Node;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.c.preprocessor.AliasVar;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

public interface HeapEncoding {
	ArrayType getSizeArrType();
	
	Type getAddressType();
	
	Type getValueType();
	
	Expression freshAddress(String varName, Node varNode);	
	
	Expression freshRegion(String regionName, Node regionNode);
	
	ArrayExpression updateSizeArr(ArrayExpression sizeArr, Expression lval, Expression rval);
	
	Iterable<Iterable<Expression>> getMemoryVarSets();
		
	ImmutableSet<BooleanExpression> disjointMemLayout();
	
	ImmutableSet<BooleanExpression> disjointMemLayout(
			Iterable<Iterable<Expression>> varSets,
			ArrayExpression sizeArr);
	
	ImmutableSet<BooleanExpression> validMemAccess(
			Iterable<Iterable<Expression>> varSets,
			ArrayExpression sizeArr, Expression ptr);
	
	ImmutableSet<BooleanExpression> validMemAccess(
			Iterable<Iterable<Expression>> varSets,
			ArrayExpression sizeArr, Expression ptr, Expression size);
	
	ImmutableSet<BooleanExpression> validMemAccess(ArrayExpression sizeArr,
			Expression ptr);
	
	ImmutableSet<BooleanExpression> validMemAccess(ArrayExpression sizeArr,
			Expression ptr, Expression size);
	
	BooleanExpression validMalloc(final Iterable<Expression> heapVars, 
			ArrayExpression sizeArr, Expression ptr, Expression size);
	
	BooleanExpression validMalloc(ArrayExpression sizeArr, Expression ptr,
			Expression size);
	
	BooleanExpression validFree(ArrayExpression sizeArr, Expression ptr);
	
	Expression getConstSizeArr(ArrayType sizeArrType);
	
	Expression getValueZero();
	
	Expression getUnknownValue();
	
	Expression getUnknownAddress();
	
	Expression getNullAddress();
	
	Iterable<Iterable<Expression>> getCategorizedVars(
			Iterable<AliasVar> equivVars);
}
