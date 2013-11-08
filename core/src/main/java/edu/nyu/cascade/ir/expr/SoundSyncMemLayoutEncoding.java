package edu.nyu.cascade.ir.expr;

import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.Type;

public class SoundSyncMemLayoutEncoding implements IRSoundMemLayoutEncoding {
	
	private final Type ptrType, refType;
	private final Type valueType;
	private final SynchronousHeapEncoding heapEncoding;
	
	private SoundSyncMemLayoutEncoding(SynchronousHeapEncoding heapEncoding) {
		this.heapEncoding = heapEncoding;
		ptrType = heapEncoding.getAddressType();
		valueType = heapEncoding.getValueType().asBitVectorType();
		refType = ptrType.asTuple().getElementTypes().get(0);
	}
	
	protected static SoundSyncMemLayoutEncoding create(SynchronousHeapEncoding heapEncoding) {
		return new SoundSyncMemLayoutEncoding(heapEncoding);
	}
	
	private ExpressionManager getExpressionManager() {
		return heapEncoding.getExpressionManager();
	}
	
	private ExpressionEncoding getExpressionEncoding() {
		return heapEncoding.getExpressionEncoding();
	}
	
	@Override
  public BooleanExpression validFree(ArrayExpression sizeArr, Expression ptr) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(refType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		
		ExpressionManager exprManager = getExpressionManager();
		Expression ptrRef = ptr.asTuple().index(0);
    Expression ptrSize = sizeArr.index(ptrRef);
    Expression nullPtr = heapEncoding.getNullAddress();
    Expression sizeZro = heapEncoding.getValueZero();
    
    return exprManager.or(ptr.eq(nullPtr), exprManager.greaterThan(ptrSize, sizeZro));
  }

	@Override
	public ImmutableSet<BooleanExpression> disjointMemLayout(
			MemoryVarSets varSets, ArrayExpression sizeArr) {
		
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    Iterable<Expression> stVars = varSets.getStackVars();
    Iterable<Expression> stRegs = varSets.getStackRegions();
    Iterable<Expression> hpRegs = varSets.getHeapRegions();
		
		ExpressionManager exprManager = getExpressionManager();

		try {
			Expression nullRef = heapEncoding.getNullAddress().getChild(0);
			
	    ImmutableList<Expression> distinctRefs = new ImmutableList.Builder<Expression>()
	        .addAll(stVars).addAll(stRegs).add(nullRef).build();
	    if(distinctRefs.size() > 1) 
	    	builder.add(exprManager.distinct(distinctRefs));
	    
			if(sizeArr != null) {
				Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(refType));
				Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
	      
	      /* Disjoint of the heap region or stack region/variable */
	      for (Expression region : hpRegs) {
//	        Expression regionSize = sizeArr.index(region);
	        
	        /* Disjoint of the heap region or stack variable */
	        for (Expression lval : stVars) {
	          builder.add(
	          		exprManager.implies(
	  	              /* heap region is non-null (and not freed before),
	  	               * even freed should not be equal to lval
	  	               */
//	          				exprManager.and(region.neq(nullRef), regionSize.neq(sizeZro)),
	          				region.neq(nullRef),
	          				lval.neq(region)));
	        }
	        
	        /* Disjoint of the heap region or stack region */
	        for (Expression region2 : stRegs) {
	          builder.add(
	          		exprManager.implies(
	  	              /* heap region is non-null (and not freed before),
	  	               * even freed should not be equal to lval
	  	               */
//	          				exprManager.and(region.neq(nullRef), regionSize.neq(sizeZro)),
	          				region.neq(nullRef),
	          				region2.neq(region)));
	        }
	      }
			}
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return builder.build();
	}

	@Override
	public ImmutableSet<BooleanExpression> validMemAccess(
			MemoryVarSets varSets, ArrayExpression sizeArr, Expression ptr) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(refType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
    Iterable<Expression> stVars = varSets.getStackVars();
    Iterable<Expression> stRegs = varSets.getStackRegions();
    Iterable<Expression> hpRegs = varSets.getHeapRegions();
		
		ExpressionManager exprManager = getExpressionManager();
		
		try {
			Expression ptrRef = ptr.asTuple().index(0);
			Expression ptrOff = ptr.asTuple().index(1);
			Expression nullRef = heapEncoding.getNullAddress().getChild(0);
			Expression sizeZro = heapEncoding.getValueZero();
			
	    for( Expression var : stVars) {
	      disjs.add( /* scalar variable: size = 0; */
	      		exprManager.and(ptrRef.eq(var), ptrOff.eq(sizeZro)));
	    }
			
	    for( Expression var : stRegs) {
	      Expression sizeVar = sizeArr.index(var);
	      disjs.add( /* aggregate variable: size > 0; */
	          exprManager.and(
	          		ptrRef.eq(var),
	          		exprManager.lessThanOrEqual(sizeZro, ptrOff),
	          		exprManager.lessThan(ptrOff, sizeVar)));
	    }
	    
	    // In any heap region
			for(Expression var : hpRegs) {
				Expression sizeVar = sizeArr.index(var);
				disjs.add(
						exprManager.and(
								var.neq(nullRef), 
								sizeVar.neq(sizeZro),
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
	public ImmutableSet<BooleanExpression> validMemAccess(
			MemoryVarSets varSets, ArrayExpression sizeArr, Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(refType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		Preconditions.checkArgument(size.getType().equals(valueType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
    Iterable<Expression> stVars = varSets.getStackVars();
    Iterable<Expression> stRegs = varSets.getStackRegions();
    Iterable<Expression> hpRegs = varSets.getHeapRegions();
		
		ExpressionManager exprManager = getExpressionManager();
		ExpressionEncoding exprEncoding = getExpressionEncoding();
		
		try {
			Expression ptrRef = ptr.asTuple().index(0);
			Expression ptrOff = ptr.asTuple().index(1);
			
//			Expression boundOff = exprManager.plus(valueType.getSize(), ptrOff, size);
			Expression boundOff = exprEncoding.plus(ptrOff, size);
			
			Expression nullRef = heapEncoding.getNullAddress().getChild(0);
			Expression sizeZro = heapEncoding.getValueZero();
			
			// In any stack variable
	    for( Expression var : stVars) {
	      disjs.add( /* scalar variable: size = 0; */
	      		exprManager.and(
	      				ptrRef.eq(var), ptrOff.eq(sizeZro), size.eq(sizeZro)));
	    }
			
	    // In any stack region
	    for( Expression var : stRegs) {
	      Expression sizeVar = sizeArr.index(var);
	      disjs.add( /* aggregate variable: size > 0; */
	          exprManager.and(
	          		ptrRef.eq(var),
	          		exprManager.greaterThanOrEqual(ptrOff, sizeZro),
	          		exprManager.lessThan(boundOff, sizeVar)));
	    }
	    
	    // In any heap region
			for(Expression var : hpRegs) {
				Expression sizeVar = sizeArr.index(var);
				disjs.add(
						exprManager.and(
								var.neq(nullRef), 
								sizeVar.neq(sizeZro)),
								ptrRef.eq(var),
								exprManager.greaterThanOrEqual(ptrOff, sizeZro),
								exprManager.lessThan(boundOff, sizeVar));
			}
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return disjs.build();
	}
	
	@Override
	public BooleanExpression validMalloc(Iterable<Expression> heapVars,
			ArrayExpression sizeArr, Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(refType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		Preconditions.checkArgument(size.getType().equals(valueType));
		
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
		ExpressionManager exprManager = getExpressionManager();
    
		try {
			Expression nullPtr = heapEncoding.getNullAddress();
			Expression nullRef = nullPtr.getChild(0);
	    Expression sizeZro = heapEncoding.getValueZero();
	    
	    Expression assump = exprManager.neq(ptr, nullPtr); // ptr != null
	    
	    /* size not overflow cannot be checked in synchronous model */
//	    builder.add(exprManager.lessThan(ptr, ptr + size));
	    
	    /* Only analyze heap part */
	    Expression ptrRef = ptr.asTuple().index(0);
	    List<Expression> heapRegs = Lists.newLinkedList(heapVars);
	    heapRegs.remove(heapRegs.size()-1);
	    
	    for(Expression var : heapRegs) {
	      Expression sizeVar = sizeArr.index(var);
	      
	      // nullRef may also have non-zero size
	      Expression assump_local = 
	      		exprManager.and(var.neq(nullRef), sizeVar.neq(sizeZro));
        
        Expression assert_local = exprManager.neq(var, ptrRef);
        
        builder.add(exprManager.implies(assump_local, assert_local));
	    }
	    return exprManager.implies(assump, exprManager.and(builder.build()));
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
	}
}
