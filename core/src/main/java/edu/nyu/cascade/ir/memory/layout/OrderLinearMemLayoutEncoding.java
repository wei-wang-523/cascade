package edu.nyu.cascade.ir.memory.layout;

import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.MemoryVarSets;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.Type;

public class OrderLinearMemLayoutEncoding implements IROrderMemLayoutEncoding {
	
	private final ExpressionEncoding exprEncoding;
	private final IRDataFormatter dataFormatter;
	private final Type addrType, sizeType;
	
	private OrderLinearMemLayoutEncoding(ExpressionEncoding exprEncoding, 
			IRDataFormatter dataFormatter) {
		this.exprEncoding = exprEncoding;
		this.dataFormatter = dataFormatter;
		addrType = dataFormatter.getAddressType();
		sizeType = dataFormatter.getSizeType();
	}
	
	public static OrderLinearMemLayoutEncoding create(ExpressionEncoding exprEncoding, 
			IRDataFormatter dataFormatter) {
		return new OrderLinearMemLayoutEncoding(exprEncoding, dataFormatter);
	}

	@Override
	public ImmutableSet<BooleanExpression> disjointMemLayout(
			MemoryVarSets varSets, ArrayExpression sizeArr, Expression lastRegion) {
		Preconditions.checkNotNull(lastRegion);
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
		
		Map<Expression, xtc.type.Type> stVarsMap = varSets.getStackVarsMap();
    
		ExpressionManager exprManager = exprEncoding.getExpressionManager();
		
		try {
      
      /* The upper bound of the stack variable won't overflow */
      for (Entry<Expression, xtc.type.Type> stVarEntry : stVarsMap.entrySet()) {
      	Expression stVar = stVarEntry.getKey();
      	xtc.type.Type stVarType = stVarEntry.getValue();
      	
      	long stVarSize = CType.getSizeofType(stVarType);
      	Expression stVarSizeExpr = exprEncoding.integerConstant(stVarSize);
      	builder.add(
      			exprEncoding.notOverflow(stVar, stVarSizeExpr).asBooleanExpression());
      }
      
      /* All the stack vars are ordered */
      Iterator<Entry<Expression, xtc.type.Type>> stVarItr = stVarsMap.entrySet().iterator();
      Expression stackBound = null;
      
      if( stVarItr.hasNext() ) {
      	stackBound = stVarItr.next().getKey();
      }
      
      while (stVarItr.hasNext()) {
        Entry<Expression, xtc.type.Type> stValEntry2 = stVarItr.next();
        Expression stVal2 = stValEntry2.getKey();
        xtc.type.Type stValType2 = stValEntry2.getValue();
        
        long stValSize2 = CType.getSizeofType(stValType2);
        Expression stValSizeExpr2 = exprEncoding.integerConstant(stValSize2);
        Expression stValBound2 = exprEncoding.plus(stVal2, stValSizeExpr2);
        builder.add(exprManager.greaterThan(stackBound, stValBound2));       
        stackBound = stVal2;
      }
      
      if(stackBound != null) {      	
      	Expression nullPtr = dataFormatter.getNullAddress();
      	if(sizeArr == null) {
      		builder.add(exprManager.greaterThan(stackBound, nullPtr));
      	} else {
      		/* lastRegionBound = lastRegion != 0 ? lastRegion + size[lastRegion] : 0; */
          Expression heapBound = exprManager.ifThenElse(
              lastRegion.neq(nullPtr),
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
		Preconditions.checkNotNull(sizeArr);
		Preconditions.checkNotNull(lastRegion);
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(sizeType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));
		Preconditions.checkArgument(size.getType().equals(sizeType));
		
		ExpressionManager exprManager = exprEncoding.getExpressionManager();
		
		try {
			Expression lastRegionBound = exprEncoding.plus(lastRegion, sizeArr.index(lastRegion));
	    Expression ptrBound = exprEncoding.plus(ptr, size);
	    
	    Expression nullPtr = dataFormatter.getNullAddress();
	    
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
		
    Map<Expression, xtc.type.Type> stVarsMap = varSets.getStackVarsMap();
    Collection<Expression> hpRegs = varSets.getHeapRegions();
    
    ExpressionManager exprManager = exprEncoding.getExpressionManager();
		
		try {
	    /* TODO: Check the scope of local variable, this will be unsound to take 
	     * address of local variable out of scope */
			
			/* In any stack variable */
	    for( Entry<Expression, xtc.type.Type> stVarEntry : stVarsMap.entrySet() ) {
	    	Expression stVar = stVarEntry.getKey();
	    	xtc.type.Type stVarType = stVarEntry.getValue();
	    	long stVarSize = CType.getSizeofType(stVarType);
	    	Expression stVarSizeExpr = exprEncoding.integerConstant(stVarSize);
	    	disjs.add(
	    			exprEncoding.within(stVar, stVarSizeExpr, ptr).asBooleanExpression());
	    }
	    
	    /* In any heap region */
	    Expression nullPtr = dataFormatter.getNullAddress();
	    Expression sizeZro = dataFormatter.getSizeZero();
	   
	    for( Expression hpReg : hpRegs ) {
	      Expression hpRegSizeExpr = sizeArr.index(hpReg);
	      disjs.add(
	          exprManager.and(
	              hpReg.neq(nullPtr),
	              hpRegSizeExpr.neq(sizeZro),
	              exprEncoding.within(hpReg, hpRegSizeExpr, ptr)));
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
		
    Map<Expression, xtc.type.Type> stVarsMap = varSets.getStackVarsMap();
    Collection<Expression> hpRegs = varSets.getHeapRegions();
		
    ExpressionManager exprManager = exprEncoding.getExpressionManager();
    
		try {
	    
	    /* In any stack variable */
	    for( Entry<Expression, xtc.type.Type> stVarEntry : stVarsMap.entrySet() ) {
	    	Expression stVar = stVarEntry.getKey();
	    	xtc.type.Type stVarType = stVarEntry.getValue();
	    	long stVarSize = CType.getSizeofType(stVarType);
	    	Expression stVarSizeExpr = exprEncoding.integerConstant(stVarSize);
	    	disjs.add(
	    			exprEncoding.within(stVar, stVarSizeExpr, ptr, size).asBooleanExpression());
	    }
	    
	    Expression nullPtr = dataFormatter.getNullAddress();
	    Expression sizeZro = dataFormatter.getSizeZero();
      
      /* In any heap region */
      for( Expression hpReg : hpRegs ) {
        Expression hpRegSizeExpr = sizeArr.index(hpReg);
        
        disjs.add(
            exprManager.and(
                hpReg.neq(nullPtr), 
                hpRegSizeExpr.neq(sizeZro),
                exprEncoding.within(hpReg, hpRegSizeExpr, ptr, size)));
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
        
    Expression nullPtr = dataFormatter.getNullAddress();
    Expression sizeZro = dataFormatter.getSizeZero();
    
    ExpressionManager exprManager = exprEncoding.getExpressionManager();
    return exprManager.or(ptr.eq(nullPtr), exprManager.greaterThan(size, sizeZro));
	}
}
