package edu.nyu.cascade.ir.expr;

import java.util.LinkedHashMap;

import xtc.tree.GNode;
import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.AliasVar;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;

public abstract class LinearHeapEncoding implements HeapEncoding {
	
	private final ExpressionManager exprManager;
	private final ExpressionEncoding encoding;
	protected final BitVectorType addrType;
	protected final BitVectorType valueType;
	private final LinkedHashMap<String, Expression> heapRegions, stackVars, stackRegions;
	
	protected LinearHeapEncoding(ExpressionEncoding encoding) {
		this.encoding = encoding;
		exprManager = encoding.getExpressionManager();
		
		int cellSize = encoding.getCellSize();
		addrType = exprManager.bitVectorType(cellSize);
		valueType = exprManager.bitVectorType(cellSize);
		
		heapRegions = Maps.newLinkedHashMap();
		stackVars = Maps.newLinkedHashMap();
		stackRegions = Maps.newLinkedHashMap();
	}

	@Override
	public ArrayType getSizeArrType() {
		return exprManager.arrayType(addrType, valueType);
	}

	@Override
	public Type getAddressType() {
		return addrType;
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
		return exprManager.bitVectorZero(addrType.getSize());
	}
	
	@Override
	public Iterable<Iterable<Expression>> getMemoryVarSets() {
		return new ImmutableList.Builder<Iterable<Expression>>()
				.add(stackVars.values())
				.add(stackRegions.values())
				.add(heapRegions.values()).build();
	}
	
	protected ExpressionManager getExpressionManager() {
		return exprManager;
	}

	protected Expression getLastRegion() {
		return Iterables.getLast(heapRegions.values(), null);
	}

	@Override
	public ArrayExpression updateSizeArr(ArrayExpression sizeArr, Expression lval,
	    Expression rval) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(lval.getType().equals(addrType));
		Preconditions.checkArgument(rval.getType().equals(valueType));
		return sizeArr.update(lval, rval);
	}

	@Override
	public ImmutableSet<BooleanExpression> validMemAccess(
			Iterable<Iterable<Expression>> varSets,
			ArrayExpression sizeArr, Expression ptr) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));
		
		ImmutableSet.Builder<BooleanExpression> disjs =
				new ImmutableSet.Builder<BooleanExpression>();
		
    Iterable<Expression> stVars = Iterables.get(varSets, 0);
    Iterable<Expression> stRegs = Iterables.get(varSets, 1);
    Iterable<Expression> hpRegs = Iterables.get(varSets, 2);
		
		try {
	    /* TODO: Check the scope of local variable, this will be unsound to take 
	     * address of local variable out of scope */
	    for( Expression stVar : stVars)    disjs.add(ptr.eq(stVar));
	    
	    // In any stack region
	    for(Expression region : stRegs) {
	      Expression regionSize = sizeArr.index(region);
	      
	      BitVectorExpression regionBound = exprManager.plus(addrType
	          .getSize(), region, regionSize);
	      disjs.add(
	          exprManager.and(
	              exprManager.lessThanOrEqual(region, ptr),
	              exprManager.lessThan(ptr, regionBound)));
	    }
	    
	    // In any heap region
	    Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
	    Expression sizeZro = exprManager.bitVectorZero(valueType.getSize());
	   
	    for( Expression region : hpRegs ) {
	      Expression regionSize = sizeArr.index(region);        
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
	public ImmutableSet<BooleanExpression> validMemAccess(
			Iterable<Iterable<Expression>> varSets,
	    ArrayExpression sizeArr, Expression ptr, Expression size) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));
		Preconditions.checkArgument(size.getType().equals(valueType));
		
		ImmutableSet.Builder<BooleanExpression> disjs = 
				new ImmutableSet.Builder<BooleanExpression>();
		
    Iterable<Expression> stVars = Iterables.get(varSets, 0);
    Iterable<Expression> stRegs = Iterables.get(varSets, 1);
    Iterable<Expression> hpRegs = Iterables.get(varSets, 2);
		
		try {
			
	    Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
	    Expression sizeZro = exprManager.bitVectorZero(valueType.getSize());
      BitVectorExpression ptrBound = exprManager.plus(addrType.getSize(), 
          ptr, size);	    
	    
			for( Expression stVar : stVars)    
        disjs.add(exprManager.and(ptr.eq(stVar), size.eq(sizeZro)));
      
      // In any stack region
      for(Expression region : stRegs) {
        Expression regionSize = sizeArr.index(region);
        BitVectorExpression regionBound = exprManager.plus(addrType.getSize(), 
            region, regionSize);
        
        disjs.add(
            exprManager.and(
                exprManager.lessThanOrEqual(region, ptr),
                exprManager.lessThan(ptrBound, regionBound)));
      }
      
      // In any heap region
      for( Expression region : hpRegs ) {
        Expression regionSize = sizeArr.index(region);
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
	public BooleanExpression validFree(ArrayExpression sizeArr, Expression ptr) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(ptr.getType().equals(addrType));
    Expression size = sizeArr.index(ptr);
    Expression nullPtr = exprManager.bitVectorZero(addrType.getSize());
    Expression sizeZro = exprManager.bitVectorZero(valueType.getSize());
    return exprManager.or(ptr.eq(nullPtr), exprManager.greaterThan(size, sizeZro));
	}

	@Override
	public Expression getConstSizeArr(ArrayType sizeArrType) {
		Preconditions.checkArgument(sizeArrType.getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArrType.getElementType().equals(valueType));
		Expression sizeZro = exprManager.bitVectorZero(valueType.getSize());
		return exprManager.storeAll(sizeZro, sizeArrType);
	}

	@Override
	public Expression freshAddress(String varName, Node varNode) {
		VariableExpression res = exprManager.variable(varName, addrType, true);
		res.setNode(GNode.cast(varNode));
		String varNodeName = varNode.getString(0);
		heapRegions.put(varNodeName + CType.getScope(varNode), res);
		return res;
	}

	@Override
	public Expression freshRegion(String regionName, Node regionNode) {
		VariableExpression res = exprManager.variable(regionName, addrType, false);
		res.setNode(GNode.cast(regionNode));
		heapRegions.put(regionName + CType.getScope(regionNode), res);
		return res;
	}

	@Override
	public Iterable<Iterable<Expression>> getCategorizedVars(
	    Iterable<AliasVar> equivVars) {
	  ImmutableList.Builder<Expression> stVarsBuilder, stRegsBuilder, hpRegsBuilder;
	  stVarsBuilder = new ImmutableList.Builder<Expression>();
	  stRegsBuilder = new ImmutableList.Builder<Expression>();
	  hpRegsBuilder = new ImmutableList.Builder<Expression>();
	
	  for(AliasVar var : equivVars) {
	  	String varName = var.getName();
	  	String varKey = new StringBuilder().append(varName)
	  			.append(var.getScope()).toString();
	    if(CType.CONSTANT.equals(varName)) continue;
	    if(stackVars.containsKey(varKey)) {
	      stVarsBuilder.add(stackVars.get(varKey));
	    } else if(stackRegions.containsKey(varKey)) {
	    	stRegsBuilder.add(stackRegions.get(varKey));
	    } else if(heapRegions.containsKey(varKey)) {
	      hpRegsBuilder.add(heapRegions.get(varKey));
	    } else {
	      IOUtils.out().println("Variable " + varName + " @" + var.getScope() + " not yet be analyzed");
	    }
	  }
	  
	  ImmutableList.Builder<Iterable<Expression>> builder = 
	      new ImmutableList.Builder<Iterable<Expression>>();
	  builder.add(stVarsBuilder.build());
	  builder.add(stRegsBuilder.build());
	  builder.add(hpRegsBuilder.build());
	  return builder.build();
	}
	
	@Override
	public Expression getUnknownValue() {
		return encoding.getIntegerEncoding().unknown(valueType);
	}

	@Override
	public Expression getUnknownAddress() {
		return encoding.getIntegerEncoding().unknown(addrType);
	}
	
	@Override
	public ImmutableSet<BooleanExpression> disjointMemLayout() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ImmutableSet<BooleanExpression> disjointMemLayout(
			Iterable<Iterable<Expression>> varSets, ArrayExpression sizeArr) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ImmutableSet<BooleanExpression> validMemAccess(ArrayExpression sizeArr,
			Expression ptr) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ImmutableSet<BooleanExpression> validMemAccess(ArrayExpression sizeArr,
			Expression ptr, Expression size) {
		// TODO Auto-generated method stub
		return null;
	}
}
