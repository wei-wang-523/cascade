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

public class SoundLinearMemLayoutEncoding implements IRSoundMemLayoutEncoding {
	
	private final ExpressionEncoding exprEncoding;
	private final IRDataFormatter dataFormatter;
	private final Type addrType, sizeType;
	
	private SoundLinearMemLayoutEncoding(ExpressionEncoding exprEncoding, 
			IRDataFormatter dataFormatter) {
		this.exprEncoding = exprEncoding;
		this.dataFormatter = dataFormatter;
		addrType = dataFormatter.getAddressType();
		sizeType = dataFormatter.getSizeType();
	}
	
	public static SoundLinearMemLayoutEncoding create(ExpressionEncoding exprEncoding, 
			IRDataFormatter dataFormatter) {
		return new SoundLinearMemLayoutEncoding(exprEncoding, dataFormatter);
	}

	@Override
  public ImmutableSet<BooleanExpression> disjointMemLayout(
  		MemoryVarSets varSets, ArrayExpression sizeArr) {
		
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
		Map<Expression, xtc.type.Type> stVarsMap = varSets.getStackVarsMap();
    Collection<Expression> hpRegs = varSets.getHeapRegions();
		
		ExpressionManager exprManager = exprEncoding.getExpressionManager();
		
		try {
			
			Expression nullPtr = dataFormatter.getNullAddress();
			Expression sizeZro = dataFormatter.getSizeZero();
	
			for(Entry<Expression, xtc.type.Type> stVarEntry1 : stVarsMap.entrySet()) {
	    	Expression stVar1 = stVarEntry1.getKey();
	    	xtc.type.Type stVarType1 = stVarEntry1.getValue();
	    	
				/* Not null */
				builder.add(stVar1.neq(nullPtr));
				
				/* The upper bound of the stack variable won't overflow. */
				long stVarSize1 = CType.getSizeofType(stVarType1);
				assert stVarSize1 >= 0;
				Expression stVarSizeExpr1 = exprEncoding.integerConstant(stVarSize1);
				
				builder.add(
						exprEncoding.notOverflow(stVar1, stVarSizeExpr1).asBooleanExpression());
				
				
				/* The size of the stack var will be larger than zero (won't be zero). */
				for (Entry<Expression, xtc.type.Type> stVarEntry2 : stVarsMap.entrySet()) {
					Expression stVar2 = stVarEntry2.getKey();
		    	xtc.type.Type stVarType2 = stVarEntry2.getValue();
					
					if (!stVar1.equals(stVar2)) {
						long stVarSize2 = CType.getSizeofType(stVarType2);
						assert stVarSize2 >= 0;
						if(stVarSize2 > 0) {
							Expression stVarSizeExpr2 = exprEncoding.integerConstant(stVarSize2);
							builder.add(
									exprEncoding.disjoint(stVar1, stVarSizeExpr1, stVar2, stVarSizeExpr2).asBooleanExpression());
						} else {
							builder.add(
									exprEncoding.disjoint(stVar1, stVarSizeExpr1, stVar2).asBooleanExpression());
						}
					}
				}
			}
	     
			if(sizeArr != null) {
	      for (Expression hpReg : hpRegs) {
	      	Expression hpRegSizeExpr = sizeArr.index(hpReg);
	        
	        /* Disjoint of the heap region or stack variable */
	        for (Entry<Expression, xtc.type.Type> stVarEntry : stVarsMap.entrySet()) {
	        	Expression stVar = stVarEntry.getKey();
	        	xtc.type.Type stVarType = stVarEntry.getValue();
	        	
						long stVarSize = CType.getSizeofType(stVarType);
						Expression stVarSizeExpr = exprEncoding.integerConstant(stVarSize);
						
						/* heap region is non-null (and not freed before), even freed should not be equal to stVar */
						builder.add(exprManager.implies(
		          		hpReg.neq(nullPtr),
		          		exprManager.ifThenElse(hpRegSizeExpr.neq(sizeZro),
		          				exprEncoding.disjoint(stVar, stVarSizeExpr, hpReg, hpRegSizeExpr),
		          				exprEncoding.disjoint(stVar, stVarSizeExpr, hpReg))));
	        }
	      }
			}
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
		return builder.build();
  }
	
	@Override
  public BooleanExpression validMalloc(MemoryVarSets varSet,
      ArrayExpression sizeArr, Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(sizeType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));
		Preconditions.checkArgument(size.getType().equals(sizeType));
		
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    
    ExpressionManager exprManager = exprEncoding.getExpressionManager();
    
    try {
			Expression nullPtr = dataFormatter.getNullAddress();
			Expression sizeZro = dataFormatter.getSizeZero();
			Expression ptrBound = exprEncoding.plus(ptr, size);
      
      Expression assump = exprManager.neq(ptr, nullPtr);
      
      /* size not overflow, but could be zero -- malloc(0) */
      builder.add(exprManager.lessThanOrEqual(ptr, ptrBound));
      
      Collection<Expression> hpRegs = varSet.getHeapRegions();
      Iterator<Expression> hpRegItr = hpRegs.iterator();
      
      for(int i = 0; i < hpRegs.size()-1; i++) { // keep the last allocated region unconsidered
      	Expression hpReg = hpRegItr.next();
        Expression hpRegSizeExpr = sizeArr.index(hpReg);
        
        /* region is not null and not freed before */
        Expression assump_local = exprManager.and( 
            exprManager.greaterThan(hpRegSizeExpr, sizeZro),
            hpReg.neq(nullPtr));
        
        /* Disjoint */
        Expression assert_local = exprEncoding.disjoint(hpReg, hpRegSizeExpr, ptr, size);
        
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
		Map<Expression, xtc.type.Type> stVarsMap = varSets.getStackVarsMap();
    Collection<Expression> hpRegs = varSets.getHeapRegions();
    
    ExpressionManager exprManager = exprEncoding.getExpressionManager();
		
		try {
	    /* TODO: Check the scope of local variable, this will be unsound to take 
	     * address of local variable out of scope */
	    for( Entry<Expression, xtc.type.Type> stVarEntry : stVarsMap.entrySet() ) {
	    	Expression stVar = stVarEntry.getKey();
	    	xtc.type.Type stVarType = stVarEntry.getValue();
	    	long stVarSize = CType.getSizeofType(stVarType);
	    	Expression stVarSizeExpr = exprEncoding.integerConstant(stVarSize);
	    	disjs.add(
	    			exprEncoding.within(stVar, stVarSizeExpr, ptr).asBooleanExpression());
	    }
	    
	    // In any heap region
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
			
			Expression nullPtr = dataFormatter.getNullAddress();
			Expression sizeZro = dataFormatter.getSizeZero();
	    
			/* In any stack region */
	    for( Entry<Expression, xtc.type.Type> stVarEntry : stVarsMap.entrySet() ) {
	    	Expression stVar = stVarEntry.getKey();
	    	xtc.type.Type stVarType = stVarEntry.getValue();
	    	
	    	long stVarSize = CType.getSizeofType(stVarType);
	    	Expression stVarSizeExpr = exprEncoding.integerConstant(stVarSize);
	    	disjs.add(
	    			exprEncoding.within(stVar, stVarSizeExpr, ptr, size).asBooleanExpression());
	    }
      
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
