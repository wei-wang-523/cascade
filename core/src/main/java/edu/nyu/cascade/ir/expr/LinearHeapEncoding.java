package edu.nyu.cascade.ir.expr;

import java.util.Collection;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;

public abstract class LinearHeapEncoding implements HeapEncoding {
	
	protected final BitVectorType addrType;
	protected final BitVectorType scalarType;
	protected final ExpressionManager exprManager;
	protected final ExpressionEncoding encoding;
	
	protected LinearHeapEncoding(ExpressionEncoding encoding) {
		this.encoding = encoding;
		exprManager = encoding.getExpressionManager();;
		int cellSize = encoding.getCellSize();
		addrType = exprManager.bitVectorType(cellSize);
		scalarType = exprManager.bitVectorType(cellSize);
	}

	@Override
	public ArrayType getSizeArrType() {
		return exprManager.arrayType(addrType, scalarType);
	}

	@Override
	public Type getAddressType() {
		return addrType;
	}

	@Override
	public Type getValueType() {
		return scalarType;
	}
	
	@Override
	public Expression getValueZero() {
		return exprManager.bitVectorZero(scalarType.getSize());
	}

	@Override
	public Expression freshAddress(String regionName, xtc.type.Type type) {
		return exprManager.variable(regionName, addrType, false);
	}

	@Override
	public boolean addToHeapRegions(Collection<Expression> heapRegions,
	    Expression region) {
		Preconditions.checkArgument(region.getType().equals(addrType));
		return heapRegions.add(region);
	}

	@Override
	public boolean addToStackVars(Collection<Expression> stackVars,
	    Expression address) {
		Preconditions.checkArgument(address.getType().equals(addrType));
		return stackVars.add(address);
	}

	@Override
	public Expression updateSizeArr(Expression sizeArr, Expression lval,
	    Expression rval) {
		Preconditions.checkArgument(sizeArr.isArray());
		Preconditions.checkArgument(lval.getType().equals(addrType));
		Preconditions.checkArgument(rval.getType().equals(scalarType));
		return sizeArr.asArray().update(lval, rval);
	}
	

	@Override
  public ImmutableSet<BooleanExpression> validStackAccess(
      Iterable<Expression> stackVars, Iterable<Expression> stackRegions,
      Expression sizeArr, Expression ptr) {
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
		try {
	    for( Expression stVar : stackVars)    disjs.add(ptr.eq(stVar));
	    
	    // In any stack region
	    for(Expression region : stackRegions) {
	      Expression regionSize = sizeArr.asArray().index(region);
	      
	      BitVectorExpression regionBound = exprManager.plus(addrType
	          .getSize(), region, regionSize);
	      disjs.add(
	          exprManager.and(
	              exprManager.lessThanOrEqual(region, ptr),
	              exprManager.lessThan(ptr, regionBound)));
	    }
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
		
		return disjs.build();
  }

	@Override
	public ImmutableSet<BooleanExpression> validStackAccess(
	    Iterable<Expression> stackVars, Iterable<Expression> stackRegions,
	    Expression sizeArr, Expression ptr, Expression size) {
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
		try {
			
			Expression sizeZro = exprManager.bitVectorZero(scalarType.getSize());
			
	    for( Expression stVar : stackVars)    
	      disjs.add(exprManager.and(ptr.eq(stVar), size.eq(sizeZro)));
	    
	    // In any stack region
	    for(Expression region : stackRegions) {
	      Expression regionSize = sizeArr.asArray().index(region);
	      BitVectorExpression ptrBound = exprManager.plus(addrType.getSize(), 
	          ptr, size);
	      BitVectorExpression regionBound = exprManager.plus(addrType.getSize(), 
	          region, regionSize);
	      
	      disjs.add(
	          exprManager.and(
	              exprManager.lessThanOrEqual(region, ptr),
	              exprManager.lessThan(ptrBound, regionBound)));
	    }
		} catch (TheoremProverException e) {
	    throw new ExpressionFactoryException(e);
	  }
		
		return disjs.build();
	}

	@Override
	public ImmutableSet<BooleanExpression> validHeapAccess(
	    Iterable<Expression> heapVars, Expression sizeArr, Expression ptr) {
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
		try {
			Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
	    Expression sizeZro = exprManager.bitVectorZero(scalarType.getSize());
	    
	    for( Expression region : heapVars ) {
	      Expression regionSize = sizeArr.asArray().index(region);        
	      BitVectorExpression regionBound = exprManager.plus(addrType.getSize(), 
	          region, regionSize);
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
	public ImmutableSet<BooleanExpression> validHeapAccess(
	    Iterable<Expression> heapVars, Expression sizeArr, Expression ptr,
	    Expression size) {
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
		try {
			Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
	    Expression sizeZro = exprManager.bitVectorZero(scalarType.getSize());
			
      for( Expression region : heapVars ) {
        Expression regionSize = sizeArr.asArray().index(region);
        BitVectorExpression ptrBound = exprManager.plus(addrType.getSize(),
            ptr, size);
        BitVectorExpression regionBound = exprManager.plus(addrType.getSize(),
            region, regionSize);
        
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
	public BooleanExpression validFree(Expression sizeArr, Expression ptr) {
		Preconditions.checkArgument(sizeArr.getType().asArrayType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().asArrayType().getElementType().equals(scalarType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));
    Expression size = sizeArr.asArray().index(ptr);
    Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
    Expression sizeZro = exprManager.bitVectorZero(scalarType.getSize());
    return exprManager.or(ptr.eq(nullPtr), exprManager.greaterThan(size, sizeZro));
	}

	@Override
	public Expression getConstSizeArr(ArrayType sizeArrType) {
		Preconditions.checkArgument(sizeArrType.getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArrType.getElementType().equals(scalarType));
		Expression sizeZro = exprManager.bitVectorZero(scalarType.getSize());
		return exprManager.storeAll(sizeZro, sizeArrType);
	}
}
