package edu.nyu.cascade.ir.expr;

import java.util.LinkedHashMap;

import xtc.tree.GNode;
import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;

public final class HeapEncoding implements IRHeapEncoding {
	
	private final ExpressionManager exprManager;
	private final ExpressionEncoding encoding;
	private final IRDataFormatter formatter;
	private final LinkedHashMap<Pair<String, String>, Expression> heapRegions, stackVars, stackRegions;
	
	private Expression lastRegion;
	private final LinkedHashMap<String, Expression> lastRegions;
	
	private final Type addrType;
	private final Type valueType;
	private final Type sizeType;

	protected HeapEncoding(ExpressionEncoding encoding, IRDataFormatter formatter) {
		this.encoding = encoding;
		this.formatter = formatter;
		exprManager = encoding.getExpressionManager();
		
		addrType = formatter.getAddressType();
		valueType = formatter.getValueType();
		sizeType = formatter.getSizeType();
		
		heapRegions = Maps.newLinkedHashMap();
		stackVars = Maps.newLinkedHashMap();
		stackRegions = Maps.newLinkedHashMap();
		
		lastRegions = Maps.newLinkedHashMap();
		lastRegion = getNullAddress();
	}
	
	public static HeapEncoding create(ExpressionEncoding encoding, 
			IRDataFormatter formatter) {
		return new HeapEncoding(encoding, formatter);
	}
	
	@Override
	public ArrayType getMemoryType() {
		return formatter.getMemoryArrayType();
	}

	@Override
	public ArrayType getSizeArrType() {
		return formatter.getSizeArrayType();
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
	public Type getSizeType() {
		return sizeType;
	}
	
	@Override
	public Expression getSizeZero() {
		return exprManager.bitVectorZero(sizeType.asBitVectorType().getSize());
	}

	/**
	 * FIXME: Cannot just call encoding.zero() to let encoding to 
	 * tell bit vector type or integer type.
	 * 
	 * Since the address type might not be same as value type,
	 * the size in reality would be larger than value type size.
	 */
	@Override
	public Expression getNullAddress() {
		return formatter.getNullAddress();
	}
	
	/**
	 * Get the cell type of the array in memory record for node with certain type
	 * FIXME: if types of equivalent class elements are not agree
	 * @param type
	 * @return array element type
	 */
	@Override
	public Type getArrayElemType(xtc.type.Type type) {
		return formatter.getArrayElemType(type);
	}
	
	@Override
	public ArrayExpression updateMemArr(ArrayExpression memArr, Expression lval,
	    Expression rval) {
		Preconditions.checkArgument(memArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(memArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(lval.getType().equals(addrType));
		return formatter.updateMemoryArray(memArr, lval, rval);
	}
	
	@Override
	public Expression indexMemArr(ArrayExpression memArr, Expression lval) {
		Preconditions.checkArgument(memArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(lval.getType().equals(addrType));
		return formatter.indexMemoryArray(memArr, lval);
	}
	
	@Override
	public ArrayExpression updateSizeArr(ArrayExpression sizeArr, Expression lval,
	    Expression rval) {
		Preconditions.checkArgument(sizeArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArr.getType().getElementType().equals(sizeType));
		Preconditions.checkArgument(lval.getType().equals(addrType));
		Preconditions.checkArgument(rval.getType().equals(sizeType));
		return formatter.updateSizeArray(sizeArr, lval, rval);
	}

	@Override
	public ArrayExpression getConstSizeArr(ArrayType sizeArrType) {
		Preconditions.checkArgument(sizeArrType.getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArrType.getElementType().equals(sizeType));
		Expression sizeZro = getSizeZero();
		return exprManager.storeAll(sizeZro, sizeArrType);
	}

	@Override
	public Expression freshAddress(String varName, IRVarInfo info, xtc.type.Type type) {
		VariableExpression res = exprManager.variable(varName, addrType, true);
		Pair<String, String> varKey = Pair.of(info.getName(),
				info.getScope().getQualifiedName());
		if(type.isArray() || type.isUnion() || type.isStruct()) {
			stackRegions.put(varKey, res);
		} else {
			stackVars.put(varKey, res);
		}
		return res;
	}

	@Override
	public Expression freshRegion(String regionName, Node regionNode) {
		VariableExpression res = exprManager.variable(regionName, addrType, false);
		res.setNode(GNode.cast(regionNode));
		Pair<String, String> varKey = Pair.of(regionName,
				CType.getScopeName(regionNode));
		heapRegions.put(varKey, res);
		return res;
	}

	@Override
	public MemoryVarSets getCategorizedVars(Iterable<IRVar> equivVars) {
	  MemoryVarSets.Builder builder = new MemoryVarSets.Builder();
	
	  for(IRVar var : equivVars) {
	  	String varName = var.getName();
	  	Pair<String, String> varKey = Pair.of(varName,
	  			var.getScope().getQualifiedName());
	    if(Identifiers.CONSTANT.equals(varName)) continue;
	    if(stackVars.containsKey(varKey)) {
	    	builder.addStackVar(stackVars.get(varKey));
	    } else if(stackRegions.containsKey(varKey)) {
	    	builder.addStackRegion(stackRegions.get(varKey));
	    } else if(heapRegions.containsKey(varKey)) {
	      builder.addHeapRegion(heapRegions.get(varKey));
	    } else {
	      IOUtils.debug().pln("Variable " + varName + " @" +
	      		var.getScope().getQualifiedName() + " not yet be analyzed");
	    }
	  }
	  
	  return builder.build();
	}
	
	@Override
	public Expression getUnknownValue(xtc.type.Type type) {
		return formatter.getUnknownValue(type);
	}
	
	@Override
	public Expression getLastRegion() {
		return lastRegion;
	}

	@Override
  public Expression getLastRegion(String name) {
		if(lastRegions.containsKey(name)) {
			return lastRegions.get(name);
		} else {
			Expression res = getNullAddress();
			lastRegions.put(name, res);
			return res;
		}
  }

	@Override
	public void updateLastRegion(Expression region) {
		lastRegion = getExpressionManager().ifThenElse(
				region.eq(getNullAddress()), lastRegion, region);
	}
	
	@Override
	public void updateLastRegion(String name, Expression region) {
		Preconditions.checkArgument(lastRegions.containsKey(name));
		Expression lastRegion = lastRegions.get(name);
		Expression lastRegionPrime = getExpressionManager().ifThenElse(
				region.eq(getNullAddress()), lastRegion, region);
		lastRegions.put(name, lastRegionPrime);
	}
	
	@Override
	public MemoryVarSets getMemVarSets() {
		return new MemoryVarSets.Builder().addHeapRegions(heapRegions.values())
				.addStackRegions(stackRegions.values())
				.addStackVars(stackVars.values()).build();
	}

	@Override
	public ExpressionManager getExpressionManager() {
		return exprManager;
	}
	
	@Override
	public ExpressionEncoding getExpressionEncoding() {
		return encoding;
	}
	
	@Override
	public IRDataFormatter getDataFormatter() {
		return formatter;
	}
	
	@Override
	public int getSizeOfVar(Expression stackVar) {
		Preconditions.checkArgument(stackVar.getNode() != null);
		Preconditions.checkArgument(CType.getType(stackVar.getNode()) != null);
		xtc.type.Type type = CType.getType(stackVar.getNode());
		return formatter.getSizeOfType(type);
	}

	@Override
  public Expression addressOf(Expression expr) {
		return formatter.addressOf(expr);
  }
}
