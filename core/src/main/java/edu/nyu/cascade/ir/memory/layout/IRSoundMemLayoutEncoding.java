package edu.nyu.cascade.ir.memory.layout;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.ir.memory.MemoryVarSets;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public interface IRSoundMemLayoutEncoding {
	
	ImmutableSet<BooleanExpression> disjointMemLayout(
			MemoryVarSets multiSets, ArrayExpression sizeArr);
	
	/**
	 * Newly-allocated region with <code>size</code> at address
	 * <code>ptr</code> do not overlap with all the allocated
	 * regions <code>heapVars</code>
	 * @param memoryVarSets
	 * @param sizeArr
	 * @param ptr
	 * @param size
	 * @return
	 */
	BooleanExpression validMalloc(MemoryVarSets memoryVarSets,
      ArrayExpression sizeArr, Expression ptr, Expression size);
	
	BooleanExpression validFree(ArrayExpression markArr, Expression ptr);
	
	ImmutableSet<BooleanExpression> validMemAccess(
			MemoryVarSets varSets, ArrayExpression sizeArr, Expression ptr);
	
	ImmutableSet<BooleanExpression> validMemAccess(
			MemoryVarSets varSets, ArrayExpression sizeArr, Expression ptr, Expression size);
}
