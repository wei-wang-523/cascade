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
import edu.nyu.cascade.prover.Expression.Kind;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;

public final class SynchronousHeapEncoding implements IRHeapEncoding {
	
	private final ExpressionManager exprManager;
	private final ExpressionEncoding encoding;
	private final LinkedHashMap<Pair<String, String>, Expression> heapRegions, stackVars, stackRegions;
	private Expression lastRegion;
	private final LinkedHashMap<String, Expression> lastRegions;
	
	private final Type ptrType;
	private final Type valueType;
	private final SyncValueType mixType;
	
	private SynchronousHeapEncoding(ExpressionEncoding encoding) {
		this.encoding = encoding;
		exprManager = encoding.getExpressionManager();
		
		ptrType = encoding.getPointerEncoding().getType();
		valueType = encoding.getIntegerEncoding().getType();
		mixType = SyncValueType.create(encoding, ptrType, valueType);
		
		heapRegions = Maps.newLinkedHashMap();
		stackVars = Maps.newLinkedHashMap();
		stackRegions = Maps.newLinkedHashMap();
		
		lastRegion = encoding.getPointerEncoding().getNullPtr().getChild(0);
		lastRegions = Maps.newLinkedHashMap();
	}
	
	public static SynchronousHeapEncoding create(ExpressionEncoding encoding) {
		return new SynchronousHeapEncoding(encoding);
	}

	@Override
	public ArrayType getSizeArrType() {
		Type refType = ptrType.asTuple().getElementTypes().get(0);
		Type offType = ptrType.asTuple().getElementTypes().get(1);
		return exprManager.arrayType(refType, offType);
	}
	
	@Override
	public ArrayType getMemoryType() {
		return exprManager.arrayType(ptrType, mixType.getType());
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
	public Expression getSizeZero() {
	  return encoding.getPointerEncoding()
	  		.asSyncPointerEncoding().getOffsetEncoding().zero();
	}
	
	@Override
	public Expression getNullAddress() {
		return encoding.getPointerEncoding().getNullPtr();
	}

	@Override
	public Type getArrayElemType(xtc.type.Type type) {
	  return mixType.getValueType(type);
	}

	@Override
	public Expression freshAddress(String name, IRVarInfo info, xtc.type.Type type) {
		Expression res = encoding.getPointerEncoding().freshPtr(name, true);
		Pair<String, String> varKey = Pair.of(info.getName(),
				info.getScope().getQualifiedName());
		if(type.isArray() || type.isUnion() || type.isStruct()) {
			stackRegions.put(varKey, res.getChild(0));
		} else {
			stackVars.put(varKey, res.getChild(0));
		}
		return res;
	}
	
	@Override
	public Expression freshRegion(String name, Node node) {
		Expression res = encoding.getPointerEncoding().freshPtr(name, false);
		res.setNode(GNode.cast(node));
		Pair<String, String> varKey = Pair.of(name, CType.getScopeName(node));
		heapRegions.put(varKey, res.getChild(0));
		return res;
	}
	
	@Override
	public ArrayExpression updateMemArr(ArrayExpression memArr, Expression lval, Expression rval) {
		Preconditions.checkArgument(memArr.getType().getIndexType().equals(ptrType));
		Preconditions.checkArgument(lval.getType().equals(ptrType));
		Type cellType = memArr.getType().getElementType();
		Expression rvalPrime = mixType.castExprToCell(rval, cellType);
		return memArr.update(lval, rvalPrime);
	}
	
	@Override
	public ArrayExpression updateSizeArr(ArrayExpression sizeArr, Expression lval, Expression rval) {
		Preconditions.checkArgument(sizeArr.getType().equals(getSizeArrType()));
		Preconditions.checkArgument(lval.getType().equals(ptrType));
		Preconditions.checkArgument(rval.getType().equals(ptrType.asTuple().getElementTypes().get(1)));
		Expression lval_ref = lval.asTuple().index(0);
		return sizeArr.update(lval_ref, rval);
	}
	
	@Override
	public Expression indexMemArr(ArrayExpression memArr, Expression lval) {
		Preconditions.checkArgument(memArr.getType().getIndexType().equals(ptrType));
		Preconditions.checkArgument(lval.getType().equals(ptrType));
		Expression cell = memArr.index(lval);
		return mixType.castCellToExpr(cell, CType.getType(lval.getNode()));
	}

	@Override
	public ArrayExpression getConstSizeArr(ArrayType sizeArrType) {
		Preconditions.checkArgument(sizeArrType.equals(getSizeArrType()));
		Expression sizeZro = getSizeZero();
		return exprManager.storeAll(sizeZro, sizeArrType);
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
	      IOUtils.debug().pln("Variable " + varName + " @"
	      		+ var.getScope().getQualifiedName() + " not yet be analyzed");
	    }
	  }
	  
	  return builder.build();
	}

	@Override
	public Expression getUnknownValue(xtc.type.Type type) {
    CellKind kind = CType.getCellKind(type);
    switch(kind) {
    case POINTER:	return encoding.getPointerEncoding().unknown();
    case SCALAR:  
    case BOOL:    return encoding.getIntegerEncoding().unknown(valueType);
    default: throw new IllegalArgumentException("Invalid kind " + kind);
    }
	}
	
	@Override
	public boolean isLinear() {
		return false;
	}
	
	@Override
	public boolean isSync() {
		return true;
	}
	
	@Override
  public LinearHeapEncoding castToLinear() {
		throw new ExpressionFactoryException("Synchrnous heap encoding cannot be casted to linear.");
  }

	@Override
  public SynchronousHeapEncoding castToSync() {
		Preconditions.checkArgument(isSync());
	  return this;
  }

	@Override
  public Expression getLastRegion() {
	  return lastRegion;
  }
	
	@Override
	public Expression getLastRegion(String name) {
	  return lastRegions.get(name);
	}

	@Override
	public void updateLastRegion(Expression region) {
		Preconditions.checkArgument(region.getType().equals(
				ptrType.asTuple().getElementTypes().get(0)));
		Expression nullRef = getNullAddress().getChild(0);
		lastRegion = getExpressionManager().ifThenElse(
				region.eq(nullRef), lastRegion, region);
	}
	
	@Override
	public void updateLastRegion(String name, Expression region) {
		Preconditions.checkArgument(lastRegions.containsKey(name));
		Preconditions.checkArgument(region.getType().equals(
				ptrType.asTuple().getElementTypes().get(0)));
		Expression lastRegion = lastRegions.get(name);
		Expression nullRef = getNullAddress().getChild(0);
		Expression lastRegionPrime = getExpressionManager().ifThenElse(
				region.eq(nullRef), lastRegion, region);
		lastRegions.put(name, lastRegionPrime);
	}

	@Override
	public MemoryVarSets getMemVarSets() {
		return new MemoryVarSets.Builder().addHeapRegions(heapRegions.values())
				.addStackRegions(stackRegions.values())
				.addStackVars(stackVars.values()).build();
	}
	
	@Override
	public Expression addressOf(Expression expr) {
		Preconditions.checkArgument(expr.getNode().hasProperty(CType.TYPE));
		if(Kind.APPLY.equals(expr.getKind())) {
      return expr.getChild(0).getChild(1);
    } else {
      xtc.type.Type contentType = CType.getType(expr.getNode());
      CellKind kind = CType.getCellKind(contentType);
      switch(kind) {
      case STRUCTORUNION:
      case ARRAY:   return expr;
      default:      return expr.getChild(1);
      }
    }
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
	public Type getSizeType() {
		return getValueType();
	}
}
