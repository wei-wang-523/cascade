package edu.nyu.cascade.ir.memory.layout;

import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;

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

public class SoundSyncMemLayoutEncoding implements IRSoundMemLayoutEncoding {
	
	private final Type ptrType, sizeType, refType;
	private final ExpressionEncoding exprEncoding;
	private final IRDataFormatter dataFormatter;
	
	private SoundSyncMemLayoutEncoding(ExpressionEncoding exprEncoding, 
			IRDataFormatter dataFormatter) {
		this.exprEncoding = exprEncoding;
		this.dataFormatter = dataFormatter;
		ptrType = dataFormatter.getAddressType();
		refType = ptrType.asTuple().getElementTypes().get(0);
		sizeType = ptrType.asTuple().getElementTypes().get(1);
	}
	
	public static SoundSyncMemLayoutEncoding create(ExpressionEncoding exprEncoding, 
			IRDataFormatter dataFormatter) {
		return new SoundSyncMemLayoutEncoding(exprEncoding, dataFormatter);
	}
	
	@Override
  public BooleanExpression validFree(ArrayExpression sizeArr, Expression ptr) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(refType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(sizeType));
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		
		Expression ptrRef = dataFormatter.getBase(ptr);
    Expression ptrSize = sizeArr.index(ptrRef);
    Expression nullPtr = dataFormatter.getNullAddress();
    Expression sizeZro = dataFormatter.getSizeZero();
    
		ExpressionManager exprManager = exprEncoding.getExpressionManager();
    return exprManager.or(ptr.eq(nullPtr), exprManager.greaterThan(ptrSize, sizeZro));
  }

	@Override
	public ImmutableSet<BooleanExpression> disjointMemLayout(
			MemoryVarSets varSets, ArrayExpression sizeArr) {
		
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    
		Map<Expression, xtc.type.Type> stVarsMap = varSets.getStackVarsMap();
    Collection<Expression> hpRegs = varSets.getHeapRegions();
		
		Iterable<Expression> stVarBases = Iterables.transform(stVarsMap.keySet(), 
				new Function<Expression, Expression>(){
			@Override
			public Expression apply(Expression stVar) {
				return dataFormatter.getBase(stVar);
			}
		});
		
		ExpressionManager exprManager = exprEncoding.getExpressionManager();

		try {
			Expression nullRef = dataFormatter.getBase(dataFormatter.getNullAddress());
			
	    ImmutableList<Expression> distinctRefs = new ImmutableList.Builder<Expression>()
	        .addAll(stVarBases).add(nullRef).build();
	    if(distinctRefs.size() > 1) 
	    	builder.add(exprManager.distinct(distinctRefs));
	    
      /* Disjoint of the heap region or stack region/variable */
      for (Expression hpReg : hpRegs) {
        Expression hpRegBase = dataFormatter.getBase(hpReg);
        /* Disjoint of the heap region or stack variable */
        for (Expression stVarBase : stVarBases) {
        	/* heap region is non-null (and not freed before), even freed should not be equal to lval */
          builder.add(
          		exprManager.implies(
          				hpRegBase.neq(nullRef),
          				stVarBase.neq(hpRegBase)));
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
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(sizeType));
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		Map<Expression, xtc.type.Type> stVarsMap = varSets.getStackVarsMap();
    Collection<Expression> hpRegs = varSets.getHeapRegions();
		
		ExpressionManager exprManager = exprEncoding.getExpressionManager();
		
		try {
			Expression ptrRef = dataFormatter.getBase(ptr);
			Expression ptrOff = ptr.asTuple().index(1);
			Expression nullRef = dataFormatter.getNullAddress().getChild(0);
			Expression sizeZro = dataFormatter.getSizeZero();
			
	    for( Entry<Expression, xtc.type.Type> stVarEntry : stVarsMap.entrySet() ) {
	    	Expression stVar = stVarEntry.getKey();
	    	xtc.type.Type stVarType = stVarEntry.getValue();
	    	Expression stVarBase = dataFormatter.getBase(stVar);
	    	long stVarSize = CType.getSizeofType(stVarType);
	      Expression stVarSizeExpr = exprEncoding.integerConstant(stVarSize);
	      disjs.add( // aggregate variable: size > 0;
	          exprManager.and(
	          		ptrRef.eq(stVarBase),
	          		exprManager.lessThanOrEqual(sizeZro, ptrOff),
	          		exprManager.lessThan(ptrOff, stVarSizeExpr)));
	    }
	    
	    /* In any heap region */
			for( Expression hpReg : hpRegs ) {
				Expression hpRegBase = dataFormatter.getBase(hpReg);
				Expression hpRegSize = sizeArr.index(hpRegBase);
				disjs.add(
						exprManager.and(
								hpRegBase.neq(nullRef), 
								hpRegSize.neq(sizeZro),
								ptrRef.eq(hpRegBase),
								exprManager.lessThanOrEqual(sizeZro, ptrOff),
								exprManager.lessThan(ptrOff, hpRegSize)));
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
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(sizeType));
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		Preconditions.checkArgument(size.getType().equals(sizeType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		Map<Expression, xtc.type.Type> stVarsMap = varSets.getStackVarsMap();
    Collection<Expression> hpRegs = varSets.getHeapRegions();
		
		ExpressionManager exprManager = exprEncoding.getExpressionManager();
		
		try {
			Expression ptrRef = dataFormatter.getBase(ptr);
			Expression ptrOff = ptr.asTuple().index(1);
			
			Expression boundOff = exprEncoding.plus(ptrOff, size);
			
			Expression nullRef = dataFormatter.getBase(
					dataFormatter.getNullAddress());
			Expression sizeZro = dataFormatter.getSizeZero();
			
			/* In any stack variable */
	    for( Entry<Expression, xtc.type.Type> stVarEntry : stVarsMap.entrySet()) {
	    	Expression stVar = stVarEntry.getKey();
	    	xtc.type.Type stVarType = stVarEntry.getValue();
	    	Expression stVarBase = dataFormatter.getBase(stVar);
	    	long stVarSize = CType.getSizeofType(stVarType);
	      Expression stVarSizeExpr = exprEncoding.integerConstant(stVarSize);
	      disjs.add( // aggregate variable: size > 0
	          exprManager.and(
	          		ptrRef.eq(stVarBase),
	          		exprManager.greaterThanOrEqual(ptrOff, sizeZro),
	          		exprManager.lessThan(boundOff, stVarSizeExpr)));
	    }
	    
	    /* In any heap region */
			for(Expression hpReg : hpRegs) {
				Expression hpRegBase = dataFormatter.getBase(hpReg);
				Expression hpRegSizeExpr = sizeArr.index(hpRegBase);
				disjs.add(
						exprManager.and(
								hpRegBase.neq(nullRef), 
								hpRegSizeExpr.neq(sizeZro)),
								ptrRef.eq(hpRegBase),
								exprManager.greaterThanOrEqual(ptrOff, sizeZro),
								exprManager.lessThan(boundOff, hpRegSizeExpr));
			}
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return disjs.build();
	}
	
	@Override
	public BooleanExpression validMalloc(MemoryVarSets varSet,
			ArrayExpression sizeArr, Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(refType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(sizeType));
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		Preconditions.checkArgument(size.getType().equals(sizeType));
		
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
		ExpressionManager exprManager = exprEncoding.getExpressionManager();
		
		try {
			Expression nullPtr = dataFormatter.getNullAddress();
			Expression nullRef = dataFormatter.getBase(nullPtr);
	    Expression sizeZro = dataFormatter.getSizeZero();
	    
	    Expression assump = exprManager.neq(ptr, nullPtr); // ptr != null
	    
	    /* size not overflow cannot be checked in synchronous model */
	    
	    /* Only analyze heap part */
	    Expression ptrRef = dataFormatter.getBase(ptr);
	    Collection<Expression> hpRegs = varSet.getHeapRegions();
	    Iterator<Expression> hpRegItr = hpRegs.iterator();
	    int lastIndex = hpRegs.size() - 1;
	    
	    for(int i = 0; i < lastIndex; i++) {
	    	Expression hpRegBase = dataFormatter.getBase(hpRegItr.next());
	      Expression hpRegSizeExpr = sizeArr.index(hpRegBase);
	      
	      Expression assump_local = // nullRef may also have non-zero size
	      		exprManager.and(hpRegBase.neq(nullRef), hpRegSizeExpr.neq(sizeZro));
        
        Expression assert_local = exprManager.neq(hpRegBase, ptrRef);
        
        builder.add(exprManager.implies(assump_local, assert_local));
	    }
	    return exprManager.implies(assump, exprManager.and(builder.build()));
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
	}
}
