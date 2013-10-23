package edu.nyu.cascade.ir.expr;

import java.util.LinkedHashMap;

import xtc.tree.GNode;
import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;

public final class LinearHeapEncoding implements IRHeapEncoding {
	
	private final ExpressionManager exprManager;
	private final ExpressionEncoding encoding;
	private final LinkedHashMap<Pair<String, String>, Expression> heapRegions, stackVars, stackRegions;
	
	private Expression lastRegion;
	private final LinkedHashMap<String, Expression> lastRegions;
	
	private final BitVectorType addrType;
	private final BitVectorType valueType;

	protected LinearHeapEncoding(ExpressionEncoding encoding) {
		this.encoding = encoding;
		exprManager = encoding.getExpressionManager();
		
		int cellSize = encoding.getCellSize();
		addrType = exprManager.bitVectorType(cellSize);
		valueType = exprManager.bitVectorType(cellSize);
		
		heapRegions = Maps.newLinkedHashMap();
		stackVars = Maps.newLinkedHashMap();
		stackRegions = Maps.newLinkedHashMap();
		
		lastRegions = Maps.newLinkedHashMap();
		lastRegion = exprManager.bitVectorZero(addrType.getSize());
	}
	
	public static LinearHeapEncoding create(ExpressionEncoding encoding) {
		return new LinearHeapEncoding(encoding);
	}
	
	@Override
	public ArrayType getMemoryType() {
		return exprManager.arrayType(addrType, valueType);
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
	
	/**
	 * Get the cell type of the array in memory record for node with certain type
	 * FIXME: if types of equivalent class elements are not agree
	 * @param type
	 * @return array element type
	 */
	@Override
	public Type getArrayElemType(xtc.type.Type type) {
	  Type resType = null;
	  switch(CType.getCellKind(type)) {
	  case SCALAR :
	  case BOOL :     resType = valueType; break;
	  case ARRAY : 
	  case POINTER :  
	  case STRUCTORUNION : resType = addrType; break;
	  default:    throw new IllegalArgumentException("Unsupported type " + type);
	  }
	  return resType;
	}

	@Override
	public boolean isLinear() {
		return true;
	}
	
	@Override
	public boolean isSync() {
		return false;
	}
	
	@Override
	public LinearHeapEncoding castToLinear() {
		return this;
	}
	
	@Override
	public SynchronousHeapEncoding castToSync() {
		throw new ExpressionFactoryException("Linear heap encoding cannot be casted to sync.");
	}
	
	@Override
	public ArrayExpression updateMemArr(ArrayExpression memArr, Expression lval,
	    Expression rval) {
		Preconditions.checkArgument(memArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(memArr.getType().getElementType().equals(valueType));
		Preconditions.checkArgument(lval.getType().equals(addrType));
		Preconditions.checkArgument(rval.getType().equals(valueType));
		return memArr.update(lval, rval);
	}
	
	@Override
	public Expression indexMemArr(ArrayExpression memArr, Expression lval) {
		Preconditions.checkArgument(memArr.getType().getIndexType().equals(addrType));
		Preconditions.checkArgument(lval.getType().equals(addrType));
		return memArr.index(lval);
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
	public ArrayExpression getConstSizeArr(ArrayType sizeArrType) {
		Preconditions.checkArgument(sizeArrType.getIndexType().equals(addrType));
		Preconditions.checkArgument(sizeArrType.getElementType().equals(valueType));
		Expression sizeZro = exprManager.bitVectorZero(valueType.getSize());
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
    CellKind kind = CType.getCellKind(type);
    switch(kind) {
    case POINTER:	return encoding.getIntegerEncoding().unknown(addrType);
    case SCALAR:  
    case BOOL:    return encoding.getIntegerEncoding().unknown(valueType);
    default: throw new IllegalArgumentException("Invalid kind " + kind);
    }
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

	protected ExpressionManager getExpressionManager() {
		return exprManager;
	}

	@Override
  public Expression addressOf(Expression expr) {
		Preconditions.checkArgument(expr.getNode() != null);
    CellKind kind = CType.getCellKind(CType.getType(expr.getNode()));
    switch(kind) {
    case STRUCTORUNION: 
    case ARRAY:   return expr;
    default:      return expr.getChild(1);
    }
  }
}
