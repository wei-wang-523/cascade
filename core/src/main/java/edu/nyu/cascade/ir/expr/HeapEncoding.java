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
	Expression freshAddress(String regionName);	
	boolean addToHeapRegions(Collection<Expression> heapRegions, Expression region);
	boolean addToStackVars(Collection<Expression> stackVars, Expression address);
	Expression updateSizeArr(Expression sizeArr, Expression lval, Expression rval);
	BooleanExpression distinctStackVars(final Collection<Expression> stackVars);
	ImmutableSet<BooleanExpression> distinctStackHeapVars(
			final Collection<Expression> heapVars,
			final Collection<Expression> stackVars);
	ImmutableSet<BooleanExpression> validStackAccess(final Collection<Expression> stackVars, 
			Expression sizeArr, Expression ptr);
	ImmutableSet<BooleanExpression> validStackAccess(final Collection<Expression> stackVars, 
			Expression sizeArr, Expression ptr, Expression size);
	ImmutableSet<BooleanExpression> validHeapAccess(final Collection<Expression> heapVars, 
			Expression sizeArr, Expression ptr);
	ImmutableSet<BooleanExpression> validHeapAccess(final Collection<Expression> heapVars, 
			Expression sizeArr, Expression ptr, Expression size);
}
