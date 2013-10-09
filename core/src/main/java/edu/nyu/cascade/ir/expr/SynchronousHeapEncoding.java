package edu.nyu.cascade.ir.expr;

import java.util.Collection;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

public class SynchronousHeapEncoding implements HeapEncoding {
	
	private final Type ptrType, scalarType, refType, offType;
	private final ExpressionManager exprManager;
	private final ExpressionEncoding encoding;
	
	private SynchronousHeapEncoding(ExpressionEncoding encoding) {
		this.encoding = encoding;
		exprManager = encoding.getExpressionManager();
		int size = encoding.getIntegerEncoding().getType().asBitVectorType().getSize();
		ptrType = encoding.getPointerEncoding().getType();
		scalarType = exprManager.bitVectorType(size);
		refType = ptrType.asTuple().getElementTypes().get(0);
		offType = ptrType.asTuple().getElementTypes().get(1);
	}
	
	protected static SynchronousHeapEncoding create(ExpressionEncoding encoding) {
		return new SynchronousHeapEncoding(encoding);
	}

	public ArrayType getSizeArrType() {
		return exprManager.arrayType(refType, scalarType);
	}
	
	public Type getAddressType() {
		return ptrType;
	}
	
	public Type getValueType() {
		return scalarType;
	}
	
	public Expression freshAddress(String name) {
		return encoding.getPointerEncoding().freshPtr(name);
	}
	
	public boolean addToHeapRegions(Collection<Expression> heapRegions, 
			Expression region) {
		Preconditions.checkArgument(region.getType().equals(ptrType));
		return heapRegions.add(region.getChild(0));
	}
	
	public Expression updateSizeArr(Expression sizeArr, Expression lval, Expression rval) {
		Preconditions.checkArgument(sizeArr.isArray());
		Preconditions.checkArgument(rval.getType().equals(scalarType));
		Expression lval_ref = lval.asTuple().index(0);
		return sizeArr.asArray().update(lval_ref, rval);
	}

	@Override
	public boolean addToStackVars(Collection<Expression> stackVars,
			Expression address) {
		Preconditions.checkArgument(address.getType().equals(ptrType));
		return stackVars.add(address.getChild(0));
	}

	@Override
	public BooleanExpression distinctStackVars(final Collection<Expression> stackVars) {
		Expression nullRef = encoding.getPointerEncoding().getNullPtr().getChild(0);
		
    ImmutableList<Expression> distinctRefs = new ImmutableList.Builder<Expression>()
        .addAll(stackVars).add(nullRef).build();
    if(distinctRefs.size() > 1) 
    	return exprManager.distinct(distinctRefs);
    else
    	return exprManager.tt();
	}

	@Override
	public ImmutableSet<BooleanExpression> distinctStackHeapVars(
			Collection<Expression> heapVars, Collection<Expression> stackVars) {
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();

		try {
			for(Expression heapRegion : heapVars) {
				for(Expression lval : stackVars) {
					builder.add(lval.neq(heapRegion));
				}
			}
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return builder.build();
	}

	@Override
	public ImmutableSet<BooleanExpression> validStackAccess(Collection<Expression> stackVars,
			Expression sizeArr,Expression ptr) {
		Preconditions.checkArgument(sizeArr.isArray());
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
		
		try {
			Expression ptrRef = ptr.asTuple().index(0);
			Expression ptrOff = ptr.asTuple().index(1);
			
			Expression sizeZro = exprManager.bitVectorZero(
					scalarType.asBitVectorType().getSize());
			
	    for( Expression var : stackVars) {
	      Expression sizeVar = sizeArr.asArray().index(var);
	      disjs.add(
	          exprManager.and(
	          		ptrRef.eq(var), 
	              /* aggregate variable: size > 0; scalar variable: size = 0 */
	              exprManager.ifThenElse( 
	                  exprManager.greaterThan(sizeVar, sizeZro),
	                  exprManager.and(
	                      exprManager.greaterThanOrEqual(ptrOff, sizeZro),
	                      exprManager.lessThan(ptrOff, sizeVar)),
	                      ptrOff.eq(sizeVar))));
	    }
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return disjs.build();
	}

	@Override
	public ImmutableSet<BooleanExpression> validHeapAccess(
			Collection<Expression> heapVars, Expression sizeArr, Expression ptr) {
		Preconditions.checkArgument(sizeArr.isArray());
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
		try {
			Expression ptrRef = ptr.asTuple().index(0);
			Expression ptrOff = ptr.asTuple().index(1);
			
			Expression nullRef = encoding.getPointerEncoding().getNullPtr().getChild(0);
			
			Expression sizeZro = exprManager.bitVectorZero(
					scalarType.asBitVectorType().getSize());
			
			for(Expression var : heapVars) {
				Expression sizeVar = sizeArr.asArray().index(var);
				disjs.add(
	          exprManager.and(
	          		var.neq(nullRef),
	              ptrRef.eq(var),
	              exprManager.lessThanOrEqual(sizeZro, ptrOff),
	              exprManager.lessThan(ptrOff, sizeVar)));
			}
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
		
		return disjs.build(); 
	}
	
	@Override
	public ImmutableSet<BooleanExpression> validStackAccess(Collection<Expression> stackVars,
			Expression sizeArr,Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.isArray());
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
		
		try {
			Expression ptrRef = ptr.asTuple().index(0);
			Expression ptrOff = ptr.asTuple().index(1);
			
			Expression sizeZro = exprManager.bitVectorZero(
					scalarType.asBitVectorType().getSize());
			
	    for( Expression var : stackVars) {
	      Expression sizeVar = sizeArr.asArray().index(var);
	      disjs.add(
	          exprManager.and(
	          		ptrRef.eq(var), 
	              /* aggregate variable: size > 0; scalar variable: size = 0 */
	              exprManager.ifThenElse( 
	                  exprManager.greaterThan(sizeVar, sizeZro),
	                  exprManager.and(
	                      exprManager.greaterThanOrEqual(ptrOff, sizeZro),
	                      exprManager.lessThan(ptrOff, sizeVar)),
	                      ptrOff.eq(sizeVar))));
	    }
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return disjs.build();
	}

	@Override
	public ImmutableSet<BooleanExpression> validHeapAccess(
			Collection<Expression> heapVars, Expression sizeArr, 
			Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.isArray());
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
		try {
			Expression ptrRef = ptr.asTuple().index(0);
			Expression ptrOff = ptr.asTuple().index(1);
			
			Expression nullRef = encoding.getPointerEncoding().getNullPtr().getChild(0);
			
			Expression sizeZro = exprManager.bitVectorZero(
					scalarType.asBitVectorType().getSize());
			
			for(Expression var : heapVars) {
				Expression sizeVar = sizeArr.asArray().index(var);
				disjs.add(
	          exprManager.and(
	          		var.neq(nullRef),
	              ptrRef.eq(var),
	              exprManager.lessThanOrEqual(sizeZro, ptrOff),
	              exprManager.lessThan(ptrOff, sizeVar)));
			}
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
		
		return disjs.build(); 
	}
}
