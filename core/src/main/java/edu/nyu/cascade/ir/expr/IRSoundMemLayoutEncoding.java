package edu.nyu.cascade.ir.expr;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public interface IRSoundMemLayoutEncoding {
	
	ImmutableSet<BooleanExpression> disjointMemLayout(
			MemoryVarSets multiSets, ArrayExpression sizeArr);
	
	BooleanExpression validMalloc(Iterable<Expression> heapVars,
      ArrayExpression sizeArr, Expression ptr, Expression size);
	
	BooleanExpression validFree(ArrayExpression sizeArr, Expression ptr);
	
	ImmutableSet<BooleanExpression> validMemAccess(
			MemoryVarSets varSets, ArrayExpression sizeArr, Expression ptr);
	
	ImmutableSet<BooleanExpression> validMemAccess(
			MemoryVarSets varSets, ArrayExpression sizeArr, Expression ptr, Expression size);
}
