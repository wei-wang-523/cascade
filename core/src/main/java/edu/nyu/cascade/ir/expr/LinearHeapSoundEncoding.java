package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;

public class LinearHeapSoundEncoding extends LinearHeapEncoding {
	
	private LinearHeapSoundEncoding(ExpressionEncoding encoding) {
		super(encoding);
	}
	
	protected static LinearHeapSoundEncoding create(ExpressionEncoding encoding) {
		return new LinearHeapSoundEncoding(encoding);
	}

	@Override
  public ImmutableSet<BooleanExpression> disjointMemLayoutSound(
  		Iterable<ImmutableList<Expression>> multiSets,
      ArrayExpression sizeArr) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));

		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
		Iterable<Expression> stackVars = Iterables.get(multiSets, 0);
		Iterable<Expression> stackRegions = Iterables.get(multiSets, 1);
		Iterable<Expression> heapRegions = Iterables.get(multiSets, 2);
		
		try {
			
			Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
			Expression sizeZro = exprManager.bitVectorZero(valueType.getSize());
	  	
			if (!Iterables.isEmpty(stackVars))  {
				ImmutableList<Expression> distinctPtr = new ImmutableList.Builder<Expression>()
            .addAll(stackVars).add(nullPtr).build();
        builder.add(exprManager.distinct(distinctPtr));
			}
	  	
			if(sizeArr != null) {
	      for (Expression region : stackRegions) {
	      	Expression regionSize = sizeArr.index(region);
	        BitVectorExpression regionBound = exprManager.plus(addrType
	            .getSize(), region, regionSize);
	        
	        /* The upper bound of the stack region won't overflow */
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
	            BitVectorExpression regionBound2 = exprManager.plus(addrType
	                .getSize(), region2, sizeArr.index(region2));
	            
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
	        BitVectorExpression regionBound = exprManager.plus(
	        		addrType.getSize(), region, regionSize);
	        
	        /* Disjoint of the heap region or stack variable */
	        for (Expression lval : stackVars) {
	          builder.add(exprManager.implies(
	              // heap region is non-null and not freed before
	              exprManager.and(region.neq(nullPtr), regionSize.neq(sizeZro)),
	              exprManager.or(
	                  exprManager.lessThan(lval, region),
	                  exprManager.lessThanOrEqual(regionBound, lval))));
	        }
	        
	        /* Disjoint of the heap region or stack region */
	        for (Expression region2 : stackRegions) {
	          BitVectorExpression regionBound2 = exprManager.plus(
	          		addrType.getSize(), region2, sizeArr.index(region2));
	          
	          builder.add(exprManager.implies(
	              // heap region is non-null and not freed before
	              exprManager.and(region.neq(nullPtr), regionSize.neq(sizeZro)),
	              exprManager.or(
	                  exprManager.lessThan(regionBound2, region),
	                  exprManager.lessThanOrEqual(regionBound, region2))));
	        }
	      }
      }
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
		return builder.build();
  }
	
	@Override
  public BooleanExpression validMallocSound(Iterable<Expression> heapVars,
      ArrayExpression sizeArr, Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));
		Preconditions.checkArgument(size.getType().equals(valueType));
		
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    
    try {
      Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
      Expression sizeZro = exprManager.bitVectorZero(valueType.getSize());
      Expression ptrBound = exprManager.plus(addrType.getSize(), ptr, size);
      
      Expression assump = exprManager.neq(ptr, nullPtr);
      
      /* size not overflow */
      builder.add(exprManager.lessThan(ptr, ptrBound));
      
      for(Expression region : heapVars) {
        Expression regionSize = sizeArr.index(region);
        Expression regionBound = exprManager.plus(addrType.getSize(), region, regionSize);
        
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
}
