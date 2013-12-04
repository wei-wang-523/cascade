package edu.nyu.cascade.ir.expr;

import java.util.Iterator;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.prover.ArrayExpression;
//import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
//import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;

public class OrderLinearMemLayoutEncoding implements IROrderMemLayoutEncoding {
	
	private LinearHeapEncoding heapEncoding;
	@SuppressWarnings("unused")
	private Type addrType, valueType, sizeType;
	
	private OrderLinearMemLayoutEncoding(LinearHeapEncoding heapEncoding) {
		this.heapEncoding = heapEncoding;
		addrType = heapEncoding.getAddressType();
		valueType = heapEncoding.getValueType();
		sizeType = heapEncoding.getSizeType();
	}
	
	protected static OrderLinearMemLayoutEncoding create(LinearHeapEncoding heapEncoding) {
		return new OrderLinearMemLayoutEncoding(heapEncoding);
	}
	
	private ExpressionManager getExpressionManager() {
		return heapEncoding.getExpressionManager();
	}
	
	private ExpressionEncoding getExpressionEncoding() {
		return heapEncoding.getExpressionEncoding();
	}

	@Override
	public ImmutableSet<BooleanExpression> disjointMemLayout(
			MemoryVarSets varSets, ArrayExpression sizeArr, Expression lastRegion) {		
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
		
    Iterable<Expression> stVars = varSets.getStackVars();
    Iterable<Expression> stRegs = varSets.getStackRegions();
    
		ExpressionManager exprManager = getExpressionManager();
		ExpressionEncoding exprEncoding = getExpressionEncoding();
		
		try {
      /* All the stack vars are ordered */

      /* The upper bound of the stack variable won't overflow */
      for (Expression stVar : stVars) {
      	int stVarSize = heapEncoding.getSizeOfVar(stVar);
      	if(stVarSize > 0) {
      		Expression stVarSizeExpr = exprManager.bitVectorConstant(
      				stVarSize, sizeType.asBitVectorType().getSize());
      		Expression stVarBound = getExpressionEncoding().plus(stVar, stVarSizeExpr);
      		builder.add(exprManager.greaterThan(stVarBound, stVar));
      	}
      }
			
			
      Iterator<Expression> stVarsItr = stVars.iterator();
      Expression stackBound = null;
      
      if( stVarsItr.hasNext() ) {
      	stackBound = stVarsItr.next();
      }

      while (stVarsItr.hasNext()) {    	
        Expression stVal2 = stVarsItr.next();
        int stValSize2 = heapEncoding.getSizeOfVar(stVal2);
        assert stValSize2 >= 0;
        
        if(stValSize2 == 0) {
        	builder.add(exprManager.greaterThan(stackBound, stVal2));   
        	stackBound = stVal2;
        } else {
        	Expression stValSizeExpr2 = exprManager.bitVectorConstant(
      				stValSize2, sizeType.asBitVectorType().getSize());      	
        	Expression stValBound = exprEncoding.plus(stVal2, stValSizeExpr2);
        	builder.add(exprManager.greaterThan(stackBound, stValBound));       
        	stackBound = stVal2;
        }
      }
      
      if(sizeArr == null) {
      	
      	if(stackBound != null) {
      		Expression nullPtr = heapEncoding.getNullAddress();
      		builder.add(exprManager.greaterThan(stackBound, nullPtr));
      	}
      	
      } else {
    		assert sizeArr.getType().getIndexType().equals(addrType);
    		assert sizeArr.getType().getElementType().equals(sizeType);
    		
        /* The upper bound of the stack region won't overflow */
        for (Expression region : stRegs) {
          Expression regionSize = sizeArr.index(region);
//          BitVectorExpression regionBound = exprManager.plus(addrType
//              .getSize(), region, regionSize);
          Expression regionBound = getExpressionEncoding().plus(region, regionSize);
          
          builder.add(exprManager.greaterThan(regionBound, region));
        }
        
        /* All the stack regions are ordered */
        Iterator<Expression> stRegsItr = stRegs.iterator();
        if( stackBound == null && stRegsItr.hasNext() ) {
        	stackBound = stRegsItr.next();
        }
        
        while (stRegsItr.hasNext()) {
          Expression stReg = stRegsItr.next();
//          Expression stRegBound = exprManager.plus(addrType.getSize(), 
//          		stReg, sizeArr.index(stReg));
          Expression stRegBound = exprEncoding.plus(stReg, sizeArr.index(stReg));
          builder.add(exprManager.greaterThan(stackBound, stRegBound));       
          stackBound = stReg;
        }
        
        if(stackBound != null) {
        	
        	Expression nullPtr = heapEncoding.getNullAddress();
          
          // lastRegionBound = lastRegion != 0 ? lastRegion + Alloc[lastRegion] : 0;
          Expression heapBound = exprManager.ifThenElse(
              lastRegion.neq(nullPtr),
//              exprManager.plus(addrType.getSize(), lastRegion, 
//              		sizeArr.index(lastRegion)),
              exprEncoding.plus(lastRegion, sizeArr.index(lastRegion)),
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
  public BooleanExpression validMalloc(ArrayExpression sizeArr, Expression lastRegion, Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(sizeType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));
		Preconditions.checkArgument(size.getType().equals(sizeType));
		
		ExpressionManager exprManager = getExpressionManager();
		ExpressionEncoding exprEncoding = getExpressionEncoding();
		
		try {
//			Expression lastRegionBound = exprManager.plus(addrType.getSize(), 
//	        lastRegion, sizeArr.index(lastRegion));
			Expression lastRegionBound = exprEncoding.plus(
	        lastRegion, sizeArr.index(lastRegion));
			
//	    Expression ptrBound = exprManager.plus(addrType.getSize(), ptr, size);
	    Expression ptrBound = exprEncoding.plus(ptr, size);
	    
	    Expression nullPtr = heapEncoding.getNullAddress();
	    
	    return exprManager.implies(
	    		ptr.neq(nullPtr),
	    		exprManager.and(
	    				exprManager.lessThanOrEqual(ptr, ptrBound), // not over flow but size could be zero
//	    				exprManager.lessThan(ptr, ptrBound),
	    				exprManager.or(
	    						lastRegion.eq(nullPtr), // last region is null (not allocated)
	    						exprManager.lessThanOrEqual(lastRegionBound, ptr)  // larger than the last allocated region
	    						)));
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
  }
	

	@Override
	public ImmutableSet<BooleanExpression> validMemAccess(
			MemoryVarSets varSets, ArrayExpression sizeArr, Expression ptr) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(sizeType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));
		
		ImmutableSet.Builder<BooleanExpression> disjs =
				new ImmutableSet.Builder<BooleanExpression>();
		
    Iterable<Expression> stVars = varSets.getStackVars();
    Iterable<Expression> stRegs = varSets.getStackRegions();
    Iterable<Expression> hpRegs = varSets.getHeapRegions();
    
    ExpressionManager exprManager = getExpressionManager();
    ExpressionEncoding exprEncoding = getExpressionEncoding();
		
		try {
	    /* TODO: Check the scope of local variable, this will be unsound to take 
	     * address of local variable out of scope */
	    for( Expression stVar : stVars) {
	    	int typeSize = heapEncoding.getSizeOfVar(stVar);
	    	assert (typeSize >= 0);
	    	if(typeSize == 0) {
	    		disjs.add(ptr.eq(stVar));
	    	} else {
					Expression typeSizeExpr = exprManager.bitVectorConstant(
							typeSize, sizeType.asBitVectorType().getSize());
					Expression varBound = exprEncoding.plus(stVar, typeSizeExpr);
	    		disjs.add(
	    				exprManager.and(
		              exprManager.lessThanOrEqual(stVar, ptr),
		              exprManager.lessThan(ptr, varBound)));
	    	}
	    }
	    
	    // In any stack region
	    for(Expression region : stRegs) {
	      Expression regionSize = sizeArr.index(region);
	      
//	      BitVectorExpression regionBound = exprManager.plus(addrType
//	          .getSize(), region, regionSize);
      Expression regionBound = exprEncoding.plus(region, regionSize);
	      
	      disjs.add(
	          exprManager.and(
	              exprManager.lessThanOrEqual(region, ptr),
	              exprManager.lessThan(ptr, regionBound)));
	    }
	    
	    // In any heap region
	    Expression nullPtr = heapEncoding.getNullAddress();
	    Expression sizeZro = heapEncoding.getSizeZero();
	   
	    for( Expression region : hpRegs ) {
	      Expression regionSize = sizeArr.index(region);        
//	      BitVectorExpression regionBound = exprManager.plus(addrType.getSize(), 
//	          region, regionSize);
	      Expression regionBound = exprEncoding.plus(region, regionSize);
	      
	      disjs.add(
	          exprManager.and(
	              region.neq(nullPtr),
	              regionSize.neq(sizeZro),
	              exprManager.lessThanOrEqual(region, ptr),
	              exprManager.lessThan(ptr, regionBound)));
	    }
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return disjs.build();
	}

	@Override
	public ImmutableSet<BooleanExpression> validMemAccess(
			MemoryVarSets varSets, ArrayExpression sizeArr, Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(sizeType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));
		Preconditions.checkArgument(size.getType().equals(sizeType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
    Iterable<Expression> stVars = varSets.getStackVars();
    Iterable<Expression> stRegs = varSets.getStackRegions();
    Iterable<Expression> hpRegs = varSets.getHeapRegions();
		
    ExpressionManager exprManager = getExpressionManager();
    ExpressionEncoding exprEncoding = getExpressionEncoding();
    
		try {
			
	    Expression nullPtr = heapEncoding.getNullAddress();
	    Expression sizeZro = heapEncoding.getSizeZero();
//      BitVectorExpression ptrBound = exprManager.plus(addrType.getSize(), 
//          ptr, size);
	    Expression ptrBound = exprEncoding.plus(ptr, size);
	    
	    for( Expression stVar : stVars) {
	    	int typeSize = heapEncoding.getSizeOfVar(stVar);
	    	assert (typeSize >= 0);
	    	if(typeSize == 0) {
	    		disjs.add(ptr.eq(stVar));
	    	} else {
					Expression typeSizeExpr = exprManager.bitVectorConstant(
							typeSize, sizeType.asBitVectorType().getSize());
					Expression varBound = exprEncoding.plus(stVar, typeSizeExpr);
	    		disjs.add(
	    				exprManager.and(
		              exprManager.lessThanOrEqual(stVar, ptr),
		              exprManager.lessThan(ptr, varBound)));
	    	}
	    }
      
      // In any stack region
      for(Expression region : stRegs) {
        Expression regionSize = sizeArr.index(region);
//        BitVectorExpression regionBound = exprManager.plus(addrType.getSize(), 
//            region, regionSize);
        Expression regionBound = exprEncoding.plus(region, regionSize);
        
        disjs.add(
            exprManager.and(
                exprManager.lessThanOrEqual(region, ptr),
                exprManager.lessThan(ptrBound, regionBound)));
      }
      
      // In any heap region
      for( Expression region : hpRegs ) {
        Expression regionSize = sizeArr.index(region);
//        BitVectorExpression regionBound = exprManager.plus(addrType.getSize(),
//            region, regionSize);
        Expression regionBound = exprEncoding.plus(region, regionSize);
        
        disjs.add(
            exprManager.and(
                region.neq(nullPtr), 
                regionSize.neq(sizeZro),
                exprManager.lessThanOrEqual(region, ptr),
                exprManager.lessThan(ptrBound, regionBound)));
      }
		} catch (TheoremProverException e) {
	    throw new ExpressionFactoryException(e);
	  }
		
		return disjs.build();
	}
	
	@Override
	public BooleanExpression validFree(ArrayExpression sizeArr, Expression ptr) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(sizeType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));
    Expression size = sizeArr.index(ptr);
    ExpressionManager exprManager = getExpressionManager();
    Expression nullPtr = heapEncoding.getNullAddress();
    Expression sizeZro = heapEncoding.getSizeZero();
    return exprManager.or(ptr.eq(nullPtr), exprManager.greaterThan(size, sizeZro));
	}
}
