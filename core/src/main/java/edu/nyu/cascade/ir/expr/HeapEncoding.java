package edu.nyu.cascade.ir.expr;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

public interface HeapEncoding {
	ArrayType getSizeArrType();
	Type getAddressType();
	Type getValueType();
	
	Expression freshAddress(String varName, xtc.type.Type varType);	
	
	Expression freshRegion(String regionName);
	
	boolean addToHeapRegions(Collection<Expression> heapRegions, Expression region);
	boolean addToStackVars(Collection<Expression> stackVars, Expression address);
	
	Expression updateSizeArr(Expression sizeArr, Expression lval, Expression rval);
	
	BooleanExpression disjointStack();
	
	ImmutableSet<BooleanExpression> disjointStackSound(
	Iterable<Expression> stackVars, Iterable<Expression> stackRegions,
	Expression sizeArr);
	ImmutableSet<BooleanExpression> disjointStackHeap();
	
	ImmutableSet<BooleanExpression> disjointStackHeapSound(
      Iterable<Expression> heapVars, Iterable<Expression> stackVars,
      Iterable<Expression> stackRegions, Expression sizeArr);
	
	ImmutableSet<BooleanExpression> disjointStackHeapOrder(
      Iterable<Expression> stackVars,
      Iterable<Expression> stackRegions, 
      Expression lastRegion, Expression sizeArr);
	
	ImmutableSet<BooleanExpression> validStackAccess(Expression sizeArr, Expression ptr);
	
	ImmutableSet<BooleanExpression> validStackAccess(
			final Iterable<Expression> stackVars, 
			final Iterable<Expression> stackRegions, 
			Expression sizeArr, Expression ptr);
	
	ImmutableSet<BooleanExpression> validStackAccess(Expression sizeArr, Expression ptr, Expression size);
	
	ImmutableSet<BooleanExpression> validStackAccess(
			final Iterable<Expression> stackVars, 
			final Iterable<Expression> stackRegions, 
			Expression sizeArr, Expression ptr, Expression size);
	
	ImmutableSet<BooleanExpression> validHeapAccess(Expression sizeArr, Expression ptr);
	
	ImmutableSet<BooleanExpression> validHeapAccess(final Iterable<Expression> heapVars, 
			Expression sizeArr, Expression ptr);
	
	ImmutableSet<BooleanExpression> validHeapAccess(Expression sizeArr, Expression ptr, Expression size);
	
	ImmutableSet<BooleanExpression> validHeapAccess(final Iterable<Expression> heapVars, 
			Expression sizeArr, Expression ptr, Expression size);
	
	BooleanExpression validMallocSound(final Iterable<Expression> heapVars, 
			Expression sizeArr, Expression ptr, Expression size);
	
	BooleanExpression validMallocSound(Expression child, Expression ptr,
			Expression size);
	
	BooleanExpression validMallocOrder(Expression lastRegion, Expression sizeArr, 
			Expression ptr, Expression size);
	
	BooleanExpression validFree(Expression sizeArr, Expression ptr);
	
	Expression getConstSizeArr(ArrayType sizeArrType);
	
	Expression getValueZero();
}
