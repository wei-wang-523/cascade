package edu.nyu.cascade.ir.expr;

import java.util.Collection;
import java.util.List;

import xtc.tree.GNode;
import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.AliasVar;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;

public class SynchronousHeapEncoding implements HeapEncoding {
	
	private final Type ptrType, refType;
	private final BitVectorType valueType, offType;
	private final ExpressionManager exprManager;
	private final ExpressionEncoding encoding;
	private final Collection<Expression> heapRegions, stackRegions, stackVars;
	
	private SynchronousHeapEncoding(ExpressionEncoding encoding) {
		this.encoding = encoding;
		exprManager = encoding.getExpressionManager();
		int cellSize = encoding.getCellSize();
		ptrType = encoding.getPointerEncoding().getType();
		valueType = exprManager.bitVectorType(cellSize);
		refType = ptrType.asTuple().getElementTypes().get(0);
		offType = ptrType.asTuple().getElementTypes().get(1).asBitVectorType();
		heapRegions = Lists.newLinkedList();
		stackVars = Sets.newHashSet();
		stackRegions = Sets.newHashSet();
		assert offType.getSize() >= valueType.getSize();
	}
	
	protected static SynchronousHeapEncoding create(ExpressionEncoding encoding) {
		return new SynchronousHeapEncoding(encoding);
	}

	@Override
	public ArrayType getSizeArrType() {
		return exprManager.arrayType(refType, valueType);
	}
	
	@Override
	public Type getAddressType() {
		return ptrType;
	}
	
	@Override
	public Type getValueType() {
		return valueType;
	}
	
	@Override
	public Expression getValueZero() {
	  return exprManager.bitVectorZero(valueType.getSize());
	}
	
	@Override
	public Expression getNullAddress() {
		return encoding.getPointerEncoding().getNullPtr();
	}

	@Override
	public Expression freshAddress(String name, Node node) {
		Expression res = encoding.getPointerEncoding().freshPtr(name);
		res.setNode(GNode.cast(node));
		stackVars.add(res.getChild(0));
		xtc.type.Type unwrappedType = CType.unwrapped(CType.getType(node));
		if(unwrappedType.isArray() || unwrappedType.isUnion() || unwrappedType.isStruct())
			stackRegions.add(res);
		return res;
	}
	
	@Override
	public Expression freshRegion(String name, Node node) {
		Expression res = encoding.getPointerEncoding().freshPtr(name);
		res.setNode(GNode.cast(node));
		heapRegions.add(res.getChild(0));
		return res;
	}
	
	@Override
	public ArrayExpression updateSizeArr(ArrayExpression sizeArr, Expression lval, Expression rval) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(refType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(lval.getType().equals(ptrType));
		Preconditions.checkArgument(rval.getType().equals(valueType));
		Expression lval_ref = lval.asTuple().index(0);
		return sizeArr.update(lval_ref, rval);
	}
	
	@Override
	public ImmutableSet<BooleanExpression> disjointMemLayout() {
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();

		try {
			Expression nullRef = encoding.getPointerEncoding().getNullPtr().getChild(0);
			
	    ImmutableList<Expression> distinctRefs = new ImmutableList.Builder<Expression>()
	        .addAll(stackVars).add(nullRef).build();
	    if(distinctRefs.size() > 1) 
	    	builder.add(exprManager.distinct(distinctRefs));
	    
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
	public ImmutableSet<BooleanExpression> validMemAccess(ArrayExpression sizeArr,Expression ptr) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(refType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
		
		try {
			Expression ptrRef = ptr.asTuple().index(0);
			Expression ptrOff = ptr.asTuple().index(1);
			Expression nullRef = encoding.getPointerEncoding().getNullPtr().getChild(0);
			Expression sizeZro = exprManager.bitVectorZero(valueType.getSize());
			
	    for( Expression var : stackVars) {
	      Expression sizeVar = sizeArr.index(var);
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
			
			for(Expression var : heapRegions) {
				Expression sizeVar = sizeArr.index(var);
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
	public ImmutableSet<BooleanExpression> validMemAccess(
			ArrayExpression sizeArr,Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(refType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		Preconditions.checkArgument(size.getType().equals(valueType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
		try {
			Expression ptrRef = ptr.asTuple().index(0);
			Expression ptrOff = ptr.asTuple().index(1);
			
			Expression boundOff = exprManager.plus(valueType.getSize(), ptrOff, size);
			
			Expression nullRef = encoding.getPointerEncoding().getNullPtr().getChild(0);
			Expression sizeZro = exprManager.bitVectorZero(valueType.getSize());
			
	    for( Expression var : stackVars) {
        Expression sizeVar = sizeArr.index(var);
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
			
			for(Expression var : heapRegions) {
				Expression sizeVar = sizeArr.index(var);
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
  public BooleanExpression validMalloc(ArrayExpression sizeArr, Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(refType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		Preconditions.checkArgument(size.getType().equals(valueType));
		
		ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    
		try {
			Expression nullPtr = encoding.getPointerEncoding().getNullPtr();
			Expression nullRef = nullPtr.getChild(0);
	    Expression sizeZro = exprManager.bitVectorZero(valueType.getSize());
	    
	    Expression assump = exprManager.neq(ptr, nullPtr); // ptr != null
	    
	    /* Only analyze heap part */
	    Expression ptrRef = ptr.asTuple().index(0);
	    List<Expression> heapRegs = Lists.newLinkedList(heapRegions);
	    heapRegs.remove(heapRegs.size()-1);
	    
	    for(Expression var : heapRegs) {
	      Expression sizeVar = sizeArr.index(var);
	      
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
  public BooleanExpression validFree(ArrayExpression sizeArr, Expression ptr) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(refType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(ptr.getType().equals(ptrType));
		
		Expression ptrRef = ptr.asTuple().index(0);
    Expression ptrSize = sizeArr.index(ptrRef);
    Expression nullPtr = encoding.getPointerEncoding().getNullPtr();
    return exprManager.or(
    		exprManager.eq(ptr, nullPtr), 
    		exprManager.greaterThan(ptrSize, 
    				exprManager.bitVectorZero(valueType.getSize())));
  }
	
	@Override
	public Expression getConstSizeArr(ArrayType sizeArrType) {
		Preconditions.checkArgument(sizeArrType.getIndexType().equals(refType));
		Preconditions.checkArgument(sizeArrType.getElementType().equals(valueType));
		Expression sizeZro = exprManager.bitVectorZero(valueType.getSize());
		return exprManager.storeAll(sizeZro, sizeArrType);
	}

	@Override
	public ImmutableSet<BooleanExpression> disjointMemLayout(
			Iterable<Iterable<Expression>> varSets, ArrayExpression sizeArr) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ImmutableSet<BooleanExpression> validMemAccess(
			Iterable<Iterable<Expression>> varSets, ArrayExpression sizeArr,
			Expression ptr) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ImmutableSet<BooleanExpression> validMemAccess(
			Iterable<Iterable<Expression>> varSets, ArrayExpression sizeArr,
			Expression ptr, Expression size) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public BooleanExpression validMalloc(Iterable<Expression> heapVars,
			ArrayExpression sizeArr, Expression ptr, Expression size) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<Iterable<Expression>> getCategorizedVars(
			Iterable<AliasVar> equivVars) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<Iterable<Expression>> getMemoryVarSets() {
		return new ImmutableList.Builder<Iterable<Expression>>()
				.add(stackVars).add(stackRegions).add(heapRegions).build();
	}

	@Override
	public Expression getUnknownValue() {
		return encoding.getIntegerEncoding().unknown(valueType);
	}
	
	@Override
	public Expression getUnknownAddress() {
		return encoding.getPointerEncoding().unknown();
	}
}
