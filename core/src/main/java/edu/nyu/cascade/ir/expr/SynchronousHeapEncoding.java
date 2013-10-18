package edu.nyu.cascade.ir.expr;

import java.util.LinkedHashMap;

import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.type.CastReference;
import xtc.type.Constant;
import xtc.type.Reference;
import xtc.type.StructOrUnionT;
import xtc.type.VariableT;

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
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;

public final class SynchronousHeapEncoding implements IRHeapEncoding {
	
	private final ExpressionManager exprManager;
	private final ExpressionEncoding encoding;
	private final LinkedHashMap<String, Expression> heapRegions, stackVars, stackRegions;
	private Expression lastRegion;
	private final LinkedHashMap<String, Expression> lastRegions;
	
	private final Type ptrType, refType;
	private final BitVectorType valueType, offType;
	
  private static final String MIX_TYPE_NAME = "mix";
  private static final String PTR_CONSTR_NAME = "ptr";
  private static final String SCALAR_CONSTR_NAME = "scalar";
  private static final String PTR_SELECTOR_NAME = "ptr-sel";
  private static final String SCALAR_SELECTOR_NAME = "scalar-sel";
  
  private final InductiveType mixType; // The list inductive data type
  private final Constructor ptrConstr, scalarConstr; // The constructors for cell type
  private final Selector ptrSel, scalarSel; // The selectors for cell type
	
	private SynchronousHeapEncoding(ExpressionEncoding encoding) {
		this.encoding = encoding;
		exprManager = encoding.getExpressionManager();
		
		int cellSize = encoding.getCellSize();
		ptrType = encoding.getPointerEncoding().getType();
		valueType = exprManager.bitVectorType(cellSize);
		refType = ptrType.asTuple().getElementTypes().get(0);
		offType = ptrType.asTuple().getElementTypes().get(1).asBitVectorType();
		
		heapRegions = Maps.newLinkedHashMap();
		stackVars = Maps.newLinkedHashMap();
		stackRegions = Maps.newLinkedHashMap();
		
		lastRegion = encoding.getPointerEncoding().getNullPtr().getChild(0);
		lastRegions = Maps.newLinkedHashMap();
		
    scalarSel = exprManager.selector(SCALAR_SELECTOR_NAME, valueType);
    scalarConstr = exprManager.constructor(SCALAR_CONSTR_NAME, scalarSel);
    
    ptrSel = exprManager.selector(PTR_SELECTOR_NAME, ptrType);
    ptrConstr = exprManager.constructor(PTR_CONSTR_NAME, ptrSel);

    mixType = exprManager.dataType(MIX_TYPE_NAME, scalarConstr, ptrConstr);
		
		assert offType.getSize() >= valueType.getSize();
	}
	
	public static SynchronousHeapEncoding create(ExpressionEncoding encoding) {
		return new SynchronousHeapEncoding(encoding);
	}

	@Override
	public ArrayType getSizeArrType() {
		return exprManager.arrayType(refType, valueType);
	}
	
	@Override
	public ArrayType getMemoryType() {
		return exprManager.arrayType(ptrType, mixType);
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
	public Type getArrayElemType(xtc.type.Type type) {
	  Type resType = null;
	  switch(CType.getCellKind(type)) {
	  case SCALAR :
	  case BOOL :     resType = valueType; break;
	  case ARRAY : {
	    xtc.type.Type contentType = CType.unwrapped(type).toArray().getType();
	    resType = getArrayElemType(contentType);
	    break;
	  }
	  case POINTER :  resType = ptrType; break;
	  case STRUCTORUNION : {
	    ElemType elemType = ElemType.getElemType(type);
	    switch(elemType) {
	    case SCALAR:  resType = valueType; break;
	    case POINTER: resType = ptrType; break;
	    default:      resType = mixType; 
	    }
	    break;
	  }
	  default:    throw new IllegalArgumentException("Unsupported type " + type);
	  }
	  return resType;
	}

	@Override
	public Expression freshAddress(String name, IRVarInfo info, xtc.type.Type type) {
		Expression res = encoding.getPointerEncoding().freshPtr(name);
		String varKey = new StringBuilder().append(info.getName())
				.append(info.getScope().getQualifiedName()).toString();
		if(type.isArray() || type.isUnion() || type.isStruct()) {
			stackRegions.put(varKey, res.getChild(0));
		} else {
			stackVars.put(varKey, res.getChild(0));
		}
		return res;
	}
	
	@Override
	public Expression freshRegion(String name, Node node) {
		Expression res = encoding.getPointerEncoding().freshPtr(name);
		res.setNode(GNode.cast(node));
		String varKey = name + CType.getScope(node);
		heapRegions.put(varKey, res.getChild(0));
		return res;
	}
	
	@Override
	public ArrayExpression updateMemArr(ArrayExpression memArr, Expression lval, Expression rval) {
		Preconditions.checkArgument(memArr.getType().getIndexType().equals(ptrType));
		Preconditions.checkArgument(lval.getType().equals(ptrType));
		Type cellType = memArr.getType().getElementType();
		Expression rvalPrime = castExprToCell(rval, cellType);
		return memArr.update(lval, rvalPrime);
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
	public Expression indexMemArr(ArrayExpression memArr, Expression lval) {
		Preconditions.checkArgument(memArr.getType().getIndexType().equals(ptrType));
		Preconditions.checkArgument(lval.getType().equals(ptrType));
		Expression cell = memArr.index(lval);
		return castCellToExpr(cell, CType.getType(lval.getNode()));
	}

	@Override
	public ArrayExpression getConstSizeArr(ArrayType sizeArrType) {
		Preconditions.checkArgument(sizeArrType.getIndexType().equals(refType));
		Preconditions.checkArgument(sizeArrType.getElementType().equals(valueType));
		Expression sizeZro = exprManager.bitVectorZero(valueType.getSize());
		return exprManager.storeAll(sizeZro, sizeArrType);
	}

	@Override
	public MemoryVarSets getCategorizedVars(Iterable<IRVar> equivVars) {
	  MemoryVarSets.Builder builder = new MemoryVarSets.Builder();
		
	  for(IRVar var : equivVars) {
	  	String varName = var.getName();
	  	String varKey = new StringBuilder().append(varName)
	  			.append(var.getScopeName()).toString();
	    if(Identifiers.CONSTANT.equals(varName)) continue;
	    if(stackVars.containsKey(varKey)) {
	    	builder.addStackVar(stackVars.get(varKey));
	    } else if(stackRegions.containsKey(varKey)) {
	    	builder.addStackRegion(stackRegions.get(varKey));
	    } else if(heapRegions.containsKey(varKey)) {
	      builder.addHeapRegion(heapRegions.get(varKey));
	    } else {
	      IOUtils.out().println("Variable " + varName + " @" + var.getScopeName() + " not yet be analyzed");
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
		Preconditions.checkArgument(region.getType().equals(refType));
		Expression nullRef = getNullAddress().getChild(0);
		lastRegion = getExpressionManager().ifThenElse(
				region.eq(nullRef), lastRegion, region);
	}
	
	@Override
	public void updateLastRegion(String name, Expression region) {
		Preconditions.checkArgument(lastRegions.containsKey(name));
		Preconditions.checkArgument(region.getType().equals(refType));
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

	protected ExpressionManager getExpressionManager() {
		return exprManager;
	}
	
	private enum ElemType {
	  SCALAR,
	  POINTER,
	  MIX;

	  static ElemType getElemType(xtc.type.Type type) {
		  Preconditions.checkArgument(CellKind.STRUCTORUNION.equals(CType.getCellKind(type)));
		  StructOrUnionT su = CType.unwrapped(type).toStructOrUnion();
		  boolean scalar = true, pointer = true;
		  for(VariableT v : su.getMembers()) {
		    switch(CType.getCellKind(v)) {
		    case SCALAR :         pointer = false; break;
		    case POINTER:         scalar = false; break;
		    // FIXME: struct { int a[100] }, get the mix types?
		    case ARRAY:
		    case STRUCTORUNION:   scalar = false; pointer = false; break;
		    default:              throw new IllegalArgumentException("Unsupported type " + v);
		    }
		  }
		  assert !(pointer && scalar);
		  if(pointer)         return  ElemType.POINTER;
		  else if(scalar)     return  ElemType.SCALAR;
		  else                return  ElemType.MIX;
		}
	}
	
	private Expression castCellToExpr(Expression pValCell, xtc.type.Type pType) {
		ExpressionManager exprManager = getExpressionManager();
		Expression resVal = pValCell;
	  if(mixType.equals(pValCell.getType())) {
	    CellKind kind = CType.getCellKind(CType.unwrapped(pType));
	    switch(kind) {
	    case SCALAR:
	    case BOOL:
	    	resVal = exprManager.select(scalarSel, pValCell); break;
	    case POINTER:
	    	resVal = exprManager.select(ptrSel, pValCell); break;
	    default:
	      throw new IllegalArgumentException("Invalid kind " + kind);
	    }
	  }
	  return resVal;
	}

	private Expression castExprToCell(Expression rval, Type cellType) {
		Preconditions.checkArgument(cellType != null);
	  if(rval.getType().equals(cellType)) return rval;
	  
	  ExpressionManager exprManager = getExpressionManager();
	  
	  if(valueType.equals(rval.getType())) {
	    if(ptrType.equals(cellType)) {
	      xtc.type.Type type = CType.getType(rval.getNode());
	      assert type.hasConstant() ;
	      Constant constant =  type.getConstant();
	      
	      if(constant.isNumber() && constant.bigIntValue().intValue() == 0) {
	        return getNullAddress();
	      }
	      
	      if(constant.isReference()) {
	        assert ((Reference) constant.getValue()).isCast();
	        CastReference ref = (CastReference) constant.getValue();
	        if(ref.getBase().isNull()) {
	          return getNullAddress();
	        }
	      }
	      
	      return encoding.getPointerEncoding().unknown();
	    } 
	    
	    if(mixType.equals(cellType)) {
	      return exprManager.construct(scalarConstr, rval);
	    }
	  } else if(ptrType.equals(rval.getType())) {
	    if(mixType.equals(cellType)) {
	      return exprManager.construct(ptrConstr, rval);
	    }
	  }
	  
	  throw new IllegalArgumentException("Invalid type " + rval.getType() + " to " + cellType);
	}
}
