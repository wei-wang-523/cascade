package edu.nyu.cascade.ir.memory;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public interface IRPartitionHeapEncoder {
	
	void addFreshRegion(String key, Expression region);

	void addFreshAddress(String key, Expression address, IRVarInfo info);

	ImmutableSet<BooleanExpression> disjointMemLayout(
			String key, ArrayExpression sizeArr);
	
	BooleanExpression validMalloc(String key,
      ArrayExpression sizeArr, Expression ptr, Expression size);	

	BooleanExpression validFree(ArrayExpression sizeArr, Expression ptr);
	
	ImmutableSet<BooleanExpression> validMemAccess(
			String key, ArrayExpression sizeArr, Expression ptr);
	
	ImmutableSet<BooleanExpression> validMemAccess(
			String key, ArrayExpression sizeArr, Expression ptr, Expression size);
}
