package edu.nyu.cascade.ir.expr;

import java.util.Iterator;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;

public class LinearHeapOrderEncoding extends LinearHeapEncoding {
	
	private LinearHeapOrderEncoding(ExpressionEncoding encoding) {
		super(encoding);
	}
	
	protected static LinearHeapOrderEncoding create(ExpressionEncoding encoding) {
		return new LinearHeapOrderEncoding(encoding);
	}

	@Override
	public ImmutableSet<BooleanExpression> disjointMemLayoutOrder(
			Iterable<ImmutableList<Expression>> varSets,
	    Expression lastRegion, ArrayExpression sizeArr) {
		Preconditions.checkArgument(Iterables.size(varSets) == 2);
		Preconditions.checkArgument(lastRegion.getType().equals(addrType));
		
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
		
		try {
      /* All the stack vars are ordered */
			ImmutableList<Expression> stackVars = Iterables.get(varSets, 0);
      Iterator<Expression> stVarsItr = stackVars.iterator();
      Expression stackBound = null;
      
      if( stVarsItr.hasNext() ) {
      	stackBound = stVarsItr.next();
      }

      while (stVarsItr.hasNext()) {
        Expression stVal2 = stVarsItr.next();
        builder.add(exprManager.greaterThan(stackBound, stVal2));   
        stackBound = stVal2;
      }
      
      if(sizeArr != null) {
        /* The upper bound of the stack region won't overflow */
        ImmutableList<Expression> stackRegions = Iterables.get(varSets, 1);
        for (Expression region : stackRegions) {
          Expression regionSize = sizeArr.index(region);
          BitVectorExpression regionBound = exprManager.plus(addrType
              .getSize(), region, regionSize);
          
          builder.add(exprManager.greaterThan(regionBound, region));
        }
        
        /* All the stack regions are ordered */
        Iterator<Expression> stRegsItr = stackRegions.iterator();
        if( stackBound == null && stRegsItr.hasNext() ) {
        	stackBound = stRegsItr.next();
        }
        
        while (stRegsItr.hasNext()) {
          Expression stReg = stRegsItr.next();
          Expression stRegBound = exprManager.plus(addrType.getSize(), 
          		stReg, sizeArr.index(stReg));
          builder.add(exprManager.greaterThan(stackBound, stRegBound));       
          stackBound = stReg;
        }
        
        if(stackBound != null) {
        	
        	Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
          
          // lastRegionBound = lastRegion != 0 ? lastRegion + Alloc[lastRegion] : 0;
          Expression heapBound = exprManager.ifThenElse(
              lastRegion.neq(nullPtr),
              exprManager.plus(addrType.getSize(), lastRegion, 
              		sizeArr.index(lastRegion)),
              nullPtr);
          
          builder.add(exprManager.greaterThan(stackBound, heapBound));
        }
      }
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
		return builder.build();
	}

	@Override
  public BooleanExpression validMallocOrder(Expression lastRegion,
  		ArrayExpression sizeArr, Expression ptr, Expression size) {
		Preconditions.checkArgument(lastRegion.getType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));
		Preconditions.checkArgument(size.getType().equals(valueType));
		
		try {
			Expression lastRegionBound = exprManager.plus(addrType.getSize(), 
	        lastRegion, sizeArr.index(lastRegion));
	    
	    Expression ptrBound = exprManager.plus(addrType.getSize(), ptr, size);
	    Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
	    
	    BooleanExpression res = exprManager.implies(
	        ptr.neq(nullPtr),
	        exprManager.and(
	            exprManager.lessThan(ptr, ptrBound), // not overflow
	            exprManager.or(
	                lastRegion.eq(nullPtr), // last region is null (not allocated)
	                exprManager.lessThanOrEqual(lastRegionBound, ptr)  // larger than the last allocated region
	                )));
	    return res;
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
  }
}
