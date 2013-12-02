package edu.nyu.cascade.ir.expr;

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.Type;

public class SoundLinearMemLayoutEncoding implements IRSoundMemLayoutEncoding {
	
	private LinearHeapEncoding heapEncoding;
	private Type addrType, valueType, sizeType;
	
	private SoundLinearMemLayoutEncoding(LinearHeapEncoding heapEncoding) {
		this.heapEncoding = heapEncoding;
		addrType = heapEncoding.getAddressType();
		valueType = heapEncoding.getValueType();
		sizeType = heapEncoding.getSizeType();
	}
	
	protected static SoundLinearMemLayoutEncoding create(LinearHeapEncoding heapEncoding) {
		return new SoundLinearMemLayoutEncoding(heapEncoding);
	}
	
	private ExpressionManager getExpressionManager() {
		return heapEncoding.getExpressionManager();
	}
	
	private ExpressionEncoding getExpressionEncoding() {
		return heapEncoding.getExpressionEncoding();
	}

	@Override
  public ImmutableSet<BooleanExpression> disjointMemLayout(
  		MemoryVarSets varSets, ArrayExpression sizeArr) {
		
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    Iterable<Expression> stackVars = varSets.getStackVars();
    Iterable<Expression> stackRegions = varSets.getStackRegions();
    Iterable<Expression> heapRegions = varSets.getHeapRegions();
		
		ExpressionManager exprManager = getExpressionManager();
		ExpressionEncoding exprEncoding = getExpressionEncoding();
		
		try {
			
			Expression nullPtr = heapEncoding.getNullAddress();
			Expression sizeZro = heapEncoding.getValueZero();
	  	
			if (!Iterables.isEmpty(stackVars))  {
				ImmutableList<Expression> distinctPtr = new ImmutableList.Builder<Expression>()
            .addAll(stackVars).add(nullPtr).build();
        builder.add(exprManager.distinct(distinctPtr));
			}
	  	
			if(sizeArr != null) {
				Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
				Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
	      for (Expression region : stackRegions) {
	      	Expression regionSize = sizeArr.index(region);
//	        BitVectorExpression regionBound = exprManager.plus(addrType
//	            .getSize(), region, regionSize);
	        Expression regionBound = exprEncoding.plus(region, regionSize);
	        
	        /* The upper bound of the stack region won't overflow.
	         * The size of the stack region will be larger than zero (won't be zero).
	         */
	        
	        builder.add(exprManager.greaterThan(regionBound, region));
	        
	        /* Every stack variable doesn't falls into any stack region*/
	        for(Expression lval : stackVars) {
	          builder.add(
	              exprManager.or(
	                  exprManager.lessThan(lval, region),
	                    exprManager.lessThanOrEqual(regionBound, lval)));
	        }
	        
	        /* Every other stack region is non-overlapping. 
	         * TODO: Could optimize using commutativity
	         */
	        for (Expression region2 : stackRegions) {
	          if (!region.equals(region2)) {
//	            BitVectorExpression regionBound2 = exprManager.plus(addrType
//	                .getSize(), region2, sizeArr.index(region2));
	          	Expression regionBound2 = exprEncoding.plus(
	          			region2, sizeArr.index(region2));
	            
	            builder.add(
	                exprManager.or(
	                    exprManager.lessThanOrEqual(regionBound2, region),
	                    exprManager.lessThanOrEqual(regionBound, region2)));
	          }
	        }
	      }
	      
	      /* Disjoint of the heap region or stack region/variable */
	      for (Expression region : heapRegions) {
	        Expression regionSize = sizeArr.index(region);
//	        BitVectorExpression regionBound = exprManager.plus(
//	        		addrType.getSize(), region, regionSize);
	        Expression regionBound = exprEncoding.plus(region, regionSize);
	        
	        /* Disjoint of the heap region or stack variable */
	        for (Expression lval : stackVars) {
	          builder.add(exprManager.implies(
	              /* heap region is non-null (and not freed before),
	               * even freed should not be equal to lval
	               */
//	              exprManager.and(region.neq(nullPtr), regionSize.neq(sizeZro)),
	          		region.neq(nullPtr),
	          		exprManager.ifThenElse(regionSize.neq(sizeZro),
	          				exprManager.or( 			// regionBound > region
	          						exprManager.lessThan(lval, region),
	          						exprManager.lessThanOrEqual(regionBound, lval)),
	          				lval.neq(region)))); 	// regionBound == region
	        }
	        
	        /* Disjoint of the heap region or stack region */
	        for (Expression region2 : stackRegions) {
	        	
	        	// regionBound2 >= region2, sizeArr[region2] >= 0
//	          BitVectorExpression regionBound2 = exprManager.plus(
//	          		addrType.getSize(), region2, sizeArr.index(region2));
	          Expression regionBound2 = exprEncoding.plus(region2, sizeArr.index(region2));
	          
	          builder.add(exprManager.implies(
	              /* heap region is non-null (and not freed before),
	               * even freed should not be equal to lval
	               */
//	              exprManager.and(region.neq(nullPtr), regionSize.neq(sizeZro)),
	          		region.neq(nullPtr),
	          		exprManager.ifThenElse(regionSize.neq(sizeZro),
	          				exprManager.or(  		// regionBound > region
	          						exprManager.lessThan(regionBound2, region),
	          						exprManager.lessThanOrEqual(regionBound, region2)),
	          				exprManager.or(  		// regionBound == region
	          						exprManager.lessThan(regionBound2, region),
	          						exprManager.lessThan(region, region2)))));
	        }
	      }
      }
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
		return builder.build();
  }
	
	@Override
  public BooleanExpression validMalloc(Iterable<Expression> heapVars,
      ArrayExpression sizeArr, Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(sizeType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));
		Preconditions.checkArgument(size.getType().equals(sizeType));
		
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    
    ExpressionManager exprManager = getExpressionManager();
    ExpressionEncoding exprEncoding = getExpressionEncoding();
    
    try {
			Expression nullPtr = heapEncoding.getNullAddress();
			Expression sizeZro = heapEncoding.getValueZero();
//      Expression ptrBound = exprManager.plus(addrType.getSize(), ptr, size);
			Expression ptrBound = exprEncoding.plus(ptr, size);
      
      Expression assump = exprManager.neq(ptr, nullPtr);
      
      /* size not overflow, but could be zero -- malloc(0) */
//      builder.add(exprManager.lessThan(ptr, ptrBound));
      builder.add(exprManager.lessThanOrEqual(ptr, ptrBound));
      
	    List<Expression> heapRegs = Lists.newLinkedList(heapVars);
	    heapRegs.remove(heapRegs.size()-1);
      
      for(Expression region : heapRegs) {
        Expression regionSize = sizeArr.index(region);
//        Expression regionBound = exprManager.plus(addrType.getSize(), region, regionSize);
        Expression regionBound = exprEncoding.plus(region, regionSize);
        
        /* region is not null and not freed before */
        Expression assump_local = exprManager.and( 
            exprManager.greaterThan(regionSize, sizeZro),
            region.neq(nullPtr));
        
        /* Disjoint */
        Expression assert_local = exprManager.or(
            exprManager.lessThanOrEqual(ptrBound, region),
            exprManager.lessThanOrEqual(regionBound, ptr));
        
        builder.add(exprManager.implies(assump_local, assert_local));
      }
      
      BooleanExpression res = exprManager.implies(assump, exprManager.and(builder.build()));
      return res;
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
	    for( Expression stVar : stVars)    disjs.add(ptr.eq(stVar));
	    
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
			Expression sizeZro = heapEncoding.getValueZero();
	   
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
			Expression sizeZro = heapEncoding.getValueZero();
//      BitVectorExpression ptrBound = exprManager.plus(addrType.getSize(), 
//          ptr, size);
			Expression ptrBound = exprEncoding.plus(ptr, size);
	    
			for( Expression stVar : stVars)    
        disjs.add(exprManager.and(ptr.eq(stVar), size.eq(sizeZro)));
      
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
		
		ExpressionManager exprManager = getExpressionManager();
    Expression size = sizeArr.index(ptr);
		Expression nullPtr = heapEncoding.getNullAddress();
		Expression sizeZro = heapEncoding.getValueZero();
    return exprManager.or(ptr.eq(nullPtr), exprManager.greaterThan(size, sizeZro));
	}
}
