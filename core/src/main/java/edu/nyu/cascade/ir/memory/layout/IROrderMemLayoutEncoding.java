package edu.nyu.cascade.ir.memory.layout;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.ir.memory.MemoryVarSets;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public interface IROrderMemLayoutEncoding {

	ImmutableSet<BooleanExpression> disjointMemLayout(MemoryVarSets multiSets,
	    ArrayExpression sizeArr, Expression lastRegion);

	BooleanExpression validMalloc(ArrayExpression sizeArr, Expression lastRegion,
	    Expression ptr, Expression size);

	BooleanExpression validFree(ArrayExpression sizeArr, Expression ptr);

	ImmutableSet<BooleanExpression> validMemAccess(MemoryVarSets varSets,
	    ArrayExpression sizeArr, Expression ptr);

	ImmutableSet<BooleanExpression> validMemAccess(MemoryVarSets varSets,
	    ArrayExpression sizeArr, Expression ptr, Expression size);
}
