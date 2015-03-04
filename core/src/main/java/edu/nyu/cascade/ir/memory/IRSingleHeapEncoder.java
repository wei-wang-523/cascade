package edu.nyu.cascade.ir.memory;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public interface IRSingleHeapEncoder {
	
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

	void addFreshAddress(Expression lval, IRVarInfo info);
	
	void addFreshRegion(Expression region);

	void reset();
}
