package edu.nyu.cascade.ir.expr;

import xtc.tree.Node;

import com.google.common.collect.ImmutableList;
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
		
	ImmutableSet<BooleanExpression> disjointMemLayoutSound();
	
	ImmutableSet<BooleanExpression> disjointMemLayoutSound(
			Iterable<ImmutableList<Expression>> varSets,
			ArrayExpression sizeArr);
	
	/**
	 * Unsound allocation encoding: just pick an order and assert that
   * the stack variables and regions, heap regions are allocated
   * in that order
   * 
	 * @param varSets
	 * @param lastRegion
	 * @param sizeArr
	 * @return
	 */
	ImmutableSet<BooleanExpression> disjointMemLayoutOrder(
			Iterable<ImmutableList<Expression>> varSets,
			Expression lastRegion, ArrayExpression sizeArr);
	
	ImmutableSet<BooleanExpression> validMemAccess(
			Iterable<ImmutableList<Expression>> varSets,
			ArrayExpression sizeArr, Expression ptr);
	
	ImmutableSet<BooleanExpression> validMemAccess(
			Iterable<ImmutableList<Expression>> varSets,
			ArrayExpression sizeArr, Expression ptr, Expression size);
	
	ImmutableSet<BooleanExpression> validMemAccess(ArrayExpression sizeArr,
			Expression ptr);
	
	ImmutableSet<BooleanExpression> validMemAccess(ArrayExpression sizeArr,
			Expression ptr, Expression size);
	
	BooleanExpression validMallocSound(final Iterable<Expression> heapVars, 
			ArrayExpression sizeArr, Expression ptr, Expression size);
	
	BooleanExpression validMallocSound(ArrayExpression sizeArr, Expression ptr,
			Expression size);
	
	BooleanExpression validMallocOrder(Expression lastRegion, ArrayExpression sizeArr, 
			Expression ptr, Expression size);
	
	BooleanExpression validFree(ArrayExpression sizeArr, Expression ptr);
	
	Expression getConstSizeArr(ArrayType sizeArrType);
	
	Expression getValueZero();
	
	Expression getNullAddress();
	
	Iterable<ImmutableList<Expression>> getCategorizedVars(
			Iterable<AliasVar> equivVars);
}
