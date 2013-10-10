package edu.nyu.cascade.ir.expr;

import java.util.Collection;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;

public class SynchronousHeapEncoding implements HeapEncoding {
	
	private final Type ptrType, refType;
	private final BitVectorType scalarType, offType;
	private final ExpressionManager exprManager;
	private final ExpressionEncoding encoding;
	private final Collection<Expression> heapRegions, stackRegions, stackVars;
	
	private SynchronousHeapEncoding(ExpressionEncoding encoding) {
		this.encoding = encoding;
		exprManager = encoding.getExpressionManager();
		int cellSize = encoding.getCellSize();
		ptrType = encoding.getPointerEncoding().getType();
		scalarType = exprManager.bitVectorType(cellSize);
		refType = ptrType.asTuple().getElementTypes().get(0);
		offType = ptrType.asTuple().getElementTypes().get(1).asBitVectorType();
		heapRegions = Lists.newLinkedList();
		stackVars = Sets.newHashSet();
		stackRegions = Sets.newHashSet();
		assert offType.getSize() > scalarType.getSize();
	}
	
	protected static SynchronousHeapEncoding create(ExpressionEncoding encoding) {
		return new SynchronousHeapEncoding(encoding);
	}

	public ArrayType getSizeArrType() {
		return exprManager.arrayType(refType, scalarType);
	}
	
	public Type getAddressType() {
		return ptrType;
	}
	
	public Type getValueType() {
		return scalarType;
	}
	
	@Override
	public Expression getValueZero() {
	  return exprManager.bitVectorZero(scalarType.getSize());
	}

	@Override
	public Expression freshAddress(String name, xtc.type.Type type) {
		Expression res = encoding.getPointerEncoding().freshPtr(name);
		stackVars.add(res.getChild(0));
		xtc.type.Type unwrappedType = CType.unwrapped(type);
		if(unwrappedType.isArray() 
				|| unwrappedType.isUnion() 
				|| unwrappedType.isStruct())
			stackRegions.add(res);
		return res;
	}
	
	@Override
	public Expression freshRegion(String name) {
		Expression res = encoding.getPointerEncoding().freshPtr(name);
		heapRegions.add(res.getChild(0));
		return res;
	}
	
	@Override
	public Expression updateSizeArr(Expression sizeArr, Expression lval, Expression rval) {
		Preconditions.checkArgument(sizeArr.isArray());
		Preconditions.checkArgument(lval.getType().equals(ptrType));
		Preconditions.checkArgument(rval.getType().equals(scalarType));
		Expression lval_ref = lval.asTuple().index(0);
		return sizeArr.asArray().update(lval_ref, rval);
	}

	@Override
	public BooleanExpression disjointStack() {
		Expression nullRef = encoding.getPointerEncoding().getNullPtr().getChild(0);
		
    ImmutableList<Expression> distinctRefs = new ImmutableList.Builder<Expression>()
        .addAll(stackVars).add(nullRef).build();
    if(distinctRefs.size() > 1) 
    	return exprManager.distinct(distinctRefs);
    else
    	return exprManager.tt();
	}

	@Override
	public ImmutableSet<BooleanExpression> disjointStackHeap() {
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();

		try {
			for(Expression heapRegion : heapRegions) {
				for(Expression lval : stackVars) {
					builder.add(lval.neq(heapRegion));
				}
			}
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return builder.build();
	}

	@Override
	public ImmutableSet<BooleanExpression> validStackAccess(Expression sizeArr,Expression ptr) {
		Preconditions.checkArgument(sizeArr.isArray());
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
		
		try {
			Expression ptrRef = ptr.asTuple().index(0);
			Expression ptrOff = ptr.asTuple().index(1);
			
			Expression sizeZro = exprManager.bitVectorZero(scalarType.getSize());
			
	    for( Expression var : stackVars) {
	      Expression sizeVar = sizeArr.asArray().index(var);
	      disjs.add(
	          exprManager.and(
	          		ptrRef.eq(var), 
	              /* aggregate variable: size > 0; scalar variable: size = 0 */
	              exprManager.ifThenElse( 
	                  exprManager.greaterThan(sizeVar, sizeZro),
	                  exprManager.and(
	                      exprManager.greaterThanOrEqual(ptrOff, sizeZro),
	                      exprManager.lessThan(ptrOff, sizeVar)),
	                      ptrOff.eq(sizeVar))));
	    }
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return disjs.build();
	}

	@Override
	public ImmutableSet<BooleanExpression> validHeapAccess(
			Expression sizeArr, Expression ptr) {
		Preconditions.checkArgument(sizeArr.isArray());
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
		try {
			Expression ptrRef = ptr.asTuple().index(0);
			Expression ptrOff = ptr.asTuple().index(1);
			
			Expression nullRef = encoding.getPointerEncoding().getNullPtr().getChild(0);
			
			Expression sizeZro = exprManager.bitVectorZero(scalarType.getSize());
			
			for(Expression var : heapRegions) {
				Expression sizeVar = sizeArr.asArray().index(var);
				disjs.add(
	          exprManager.and(
	          		var.neq(nullRef),
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
	public ImmutableSet<BooleanExpression> validStackAccess(
			Expression sizeArr,Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.isArray());
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		Preconditions.checkArgument(size.getType().equals(scalarType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
		try {
			Expression ptrRef = ptr.asTuple().index(0);
			Expression ptrOff = ptr.asTuple().index(1);
			
			Expression boundOff = exprManager.plus(scalarType.getSize(), ptrOff, size);
			
			Expression sizeZro = exprManager.bitVectorZero(scalarType.getSize());
			
	    for( Expression var : stackVars) {
        Expression sizeVar = sizeArr.asArray().index(var);
        disjs.add(
            exprManager.and(
                ptrRef.eq(var), 
                /* aggregate variable: size > 0; scalar variable: size = 0 */
                exprManager.ifThenElse( 
                    exprManager.greaterThan(sizeVar, sizeZro),
                    exprManager.and(        
                        exprManager.greaterThanOrEqual(ptrOff, sizeZro),
                        exprManager.lessThan(boundOff, sizeVar)),
                        ptrOff.eq(sizeVar)))); 
	    }
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
    return disjs.build();
	}

	@Override
	public ImmutableSet<BooleanExpression> validHeapAccess(
			Expression sizeArr, Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.isArray());
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		Preconditions.checkArgument(size.getType().equals(scalarType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
		try {
			Expression ptrRef = ptr.asTuple().index(0);
			Expression ptrOff = ptr.asTuple().index(1);
			
			Expression nullRef = encoding.getPointerEncoding().getNullPtr().getChild(0);
			
			Expression boundOff = exprManager.plus(scalarType.getSize(), ptrOff, size);		
			Expression sizeZro = exprManager.bitVectorZero(scalarType.getSize());
			
			for(Expression var : heapRegions) {
				Expression sizeVar = sizeArr.asArray().index(var);
        disjs.add(
            exprManager.and(
            		var.neq(nullRef),
            		ptrRef.eq(var), 
                exprManager.lessThanOrEqual(sizeZro, ptrOff),
                exprManager.lessThan(boundOff, sizeVar)));
			}
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
		
		return disjs.build(); 
	}

	@Override
  public BooleanExpression validMallocSound(Expression sizeArr, Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.isArray());
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		Preconditions.checkArgument(size.getType().equals(scalarType));
		
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    
		try {
			Expression nullPtr = encoding.getPointerEncoding().getNullPtr();
			Expression nullRef = nullPtr.getChild(0);
	    Expression sizeZro = exprManager.bitVectorZero(scalarType.getSize());
	    
	    Expression assump = exprManager.neq(ptr, nullPtr); // ptr != null
	    
	    /* Only analyze heap part */
	    Expression ptrRef = ptr.asTuple().index(0);
	    for(Expression var : heapRegions) {
	      Expression sizeVar = sizeArr.asArray().index(var);
	      
	      Expression assump_local = exprManager.and(
            exprManager.greaterThan(sizeVar, sizeZro),
            exprManager.neq(var, nullRef)); // nullRef may also have non-zero size
        
        Expression assert_local = exprManager.neq(var, ptrRef);
        
        builder.add(exprManager.implies(assump_local, assert_local));
	    }
	    return exprManager.implies(assump, exprManager.and(builder.build()));
		} catch (TheoremProverException e) {
      throw new ExpressionFactoryException(e);
    }
  }

	@Override
  public BooleanExpression validFree(Expression sizeArr, Expression ptr) {
		Preconditions.checkArgument(sizeArr.isArray());
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		
		Expression ptrRef = ptr.asTuple().index(0);
    Expression ptrSize = sizeArr.asArray().index(ptrRef);
    Expression nullPtr = encoding.getPointerEncoding().getNullPtr();
    return exprManager.or(
    		exprManager.eq(ptr, nullPtr), 
    		exprManager.greaterThan(ptrSize, 
    				exprManager.bitVectorZero(scalarType.getSize())));
  }
	
	@Override
	public Expression getConstSizeArr(ArrayType sizeArrType) {
		Preconditions.checkArgument(sizeArrType.getIndexType().equals(refType));
		Preconditions.checkArgument(sizeArrType.getElementType().equals(scalarType));
		Expression sizeZro = exprManager.bitVectorZero(scalarType.getSize());
		return exprManager.storeAll(sizeZro, sizeArrType);
	}

	@Override
  public ImmutableSet<BooleanExpression> validStackAccess(
      Iterable<Expression> stackVars, Iterable<Expression> stackRegions,
      Expression sizeArr, Expression ptr) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public ImmutableSet<BooleanExpression> validStackAccess(
      Iterable<Expression> stackVars, Iterable<Expression> stackRegions,
      Expression sizeArr, Expression ptr, Expression size) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public BooleanExpression validMallocOrder(Expression lastRegion,
      Expression sizeArr, Expression ptr, Expression size) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
	public boolean addToStackVars(Collection<Expression> stackVars,
			Expression address) {
	  // TODO Auto-generated method stub
	  return false;
	}

	@Override
	public boolean addToHeapRegions(Collection<Expression> heapRegions, 
			Expression region) {
	  // TODO Auto-generated method stub
	  return false;
	}

	@Override
	public ImmutableSet<BooleanExpression> disjointStackSound(
	    Iterable<Expression> stackVars, Iterable<Expression> stackRegions,
	    Expression sizeArr) {
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
  public ImmutableSet<BooleanExpression> disjointStackHeapOrder(
      Iterable<Expression> stackVars, Iterable<Expression> stackRegions,
      Expression lastRegion, Expression sizeArr) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public ImmutableSet<BooleanExpression> validHeapAccess(
      Iterable<Expression> heapVars, Expression sizeArr, Expression ptr) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public ImmutableSet<BooleanExpression> validHeapAccess(
      Iterable<Expression> heapVars, Expression sizeArr, Expression ptr,
      Expression size) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public BooleanExpression validMallocSound(Iterable<Expression> heapVars,
      Expression sizeArr, Expression ptr, Expression size) {
	  // TODO Auto-generated method stub
	  return null;
  }
}
