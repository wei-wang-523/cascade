package edu.nyu.cascade.ir.expr;

import java.util.Iterator;

import com.google.common.collect.ImmutableSet;

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
	public ImmutableSet<BooleanExpression> disjointStackHeapOrder(
			Iterable<Expression> stackVars,
	    Iterable<Expression> stackRegions, 
	    Expression lastRegion, Expression sizeArr) {
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
		
		try {
      /* All the stack vars are ordered */
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
      
      /* The upper bound of the stack region won't overflow */
      for (Expression region : stackRegions) {
        Expression regionSize = sizeArr.asArray().index(region);
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
        		stReg, sizeArr.asArray().index(stReg));
        builder.add(exprManager.greaterThan(stackBound, stRegBound));       
        stackBound = stReg;
      }
      
      if(stackBound != null) {
      	
      	Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
        
        // lastRegionBound = lastRegion != 0 ? lastRegion + Alloc[lastRegion] : 0;
        Expression heapBound = exprManager.ifThenElse(
            lastRegion.neq(nullPtr),
            exprManager.plus(addrType.getSize(), lastRegion, 
            		sizeArr.asArray().index(lastRegion)),
            nullPtr);
        
        builder.add(exprManager.greaterThan(stackBound, heapBound));
      }
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
		return builder.build();
	}

	@Override
  public BooleanExpression validMallocOrder(Expression lastRegion,
      Expression sizeArr, Expression ptr, Expression size) {
		try {
			Expression lastRegionBound = exprManager.plus(addrType.getSize(), 
	        lastRegion, sizeArr.asArray().index(lastRegion));
	    
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

	@Override
	public BooleanExpression validMallocSound(Iterable<Expression> heapVars,
	    Expression sizeArr, Expression ptr, Expression size) {
	  // TODO Auto-generated method stub
	  return null;
	}
	
	@Override
  public ImmutableSet<BooleanExpression> disjointStackHeapSound(
      Iterable<Expression> heapVars, Iterable<Expression> stackVars,
      Iterable<Expression> stackRegions, Expression sizeArr) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public Expression freshRegion(String regionName) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public BooleanExpression disjointStack() {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public ImmutableSet<BooleanExpression> disjointStackHeap() {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public ImmutableSet<BooleanExpression> validStackAccess(Expression sizeArr,
      Expression ptr) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public ImmutableSet<BooleanExpression> validStackAccess(Expression sizeArr,
      Expression ptr, Expression size) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public ImmutableSet<BooleanExpression> validHeapAccess(Expression sizeArr,
      Expression ptr) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public ImmutableSet<BooleanExpression> validHeapAccess(Expression sizeArr,
      Expression ptr, Expression size) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public BooleanExpression validMallocSound(Expression child, Expression ptr,
      Expression size) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public ImmutableSet<BooleanExpression> disjointStackSound(
      Iterable<Expression> stackVars, Iterable<Expression> stackRegions,
      Expression sizeArr) {
	  // TODO Auto-generated method stub
	  return null;
  }

}
