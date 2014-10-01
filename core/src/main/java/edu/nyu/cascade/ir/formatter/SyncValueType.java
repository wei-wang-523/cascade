package edu.nyu.cascade.ir.formatter;

import xtc.type.CastReference;
import xtc.type.Constant;
import xtc.type.Reference;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.IOUtils;

/**
 * Value type created for synchronous heap encoding
 * 
 * @author Wei
 *
 */

public class SyncValueType {
	
	private final ExpressionEncoding encoding;
	
	private final TupleType ptrType;
	private final Type valueType;
  private final InductiveType mixType; // The list inductive data type
  
  private static final String MIX_TYPE_NAME = "mix";
  private static final String PTR_CONSTR_NAME = "ptr";
  private static final String SCALAR_CONSTR_NAME = "scalar";
  private static final String PTR_SELECTOR_NAME = "ptr-sel";
  private static final String SCALAR_SELECTOR_NAME = "scalar-sel";
  
  private final Constructor ptrConstr, scalarConstr; // The constructors for cell type
  private final Selector ptrSel, scalarSel; // The selectors for cell type
	
	private SyncValueType(ExpressionEncoding encoding, Type ptrType, Type valueType) {
		Preconditions.checkArgument(ptrType.isTuple());
		
		this.encoding = encoding;
		this.ptrType = ptrType.asTuple();
		this.valueType = valueType;
		
		ExpressionManager exprManager = encoding.getExpressionManager();
    scalarSel = exprManager.selector(SCALAR_SELECTOR_NAME, valueType);
    scalarConstr = exprManager.constructor(SCALAR_CONSTR_NAME, scalarSel);
    
    ptrSel = exprManager.selector(PTR_SELECTOR_NAME, ptrType);
    ptrConstr = exprManager.constructor(PTR_CONSTR_NAME, ptrSel);

    mixType = exprManager.dataType(MIX_TYPE_NAME, scalarConstr, ptrConstr);
	}
	
	public InductiveType getType() {
		return mixType;
	}
	
	public static SyncValueType create(ExpressionEncoding encoding, Type ptrType, Type valueType) {
		return new SyncValueType(encoding, ptrType, valueType);
	}
	
	protected Expression castCellToExpr(Expression expr, xtc.type.Type pType) {
		ExpressionManager exprManager = encoding.getExpressionManager();
		Expression resVal = expr;
	  if(mixType.equals(expr.getType())) {
	  	if(pType.resolve().isPointer() || pType.resolve().isArray()) {
	  		resVal = exprManager.select(ptrSel, expr);
	  	} else {
	  		resVal = exprManager.select(scalarSel, expr);
	  	}
	  }
	  return resVal;
	}
	
	protected Expression castExprToCell(Expression expr, Type cellType) {
		Preconditions.checkNotNull(cellType);
		ExpressionManager exprManager = encoding.getExpressionManager();
		
	  if(expr.getType().equals(cellType)) return expr;
	  
	  if(valueType.equals(expr.getType())) {
	    if(ptrType.equals(cellType)) {
	      xtc.type.Type type = CType.getType(expr.getNode());
	      assert type.hasConstant() ;
	      Constant constant =  type.getConstant();
	      
	      if(constant.isNumber())  
	      	return encoding.getPointerEncoding().getNullPtr();
	      
	      if(constant.isReference()) {
	        assert ((Reference) constant.getValue()).isCast();
	        CastReference ref = (CastReference) constant.getValue();
	        if(ref.getBase().isNull())
	        	return encoding.getPointerEncoding().getNullPtr();
	      }
	      
	      return encoding.getPointerEncoding().unknown();
	    } 
	    
	    if(mixType.equals(cellType)) {
	      return exprManager.construct(scalarConstr, expr);
	    }
	  } else if(ptrType.equals(expr.getType())) {
	    if(mixType.equals(cellType)) {
	      return exprManager.construct(ptrConstr, expr);
	    }
	  }
	  
	  throw new IllegalArgumentException("Invalid type " + expr.getType() + " to " + cellType);
	}
	
	protected Type getValueType(xtc.type.Type type) {
		xtc.type.Type cleanType = type.resolve();
		
		if(cleanType.isArray() || cleanType.isStruct() || cleanType.isUnion()) 
			return getValueType(CType.getCellType(cleanType));
		
		if(cleanType.isPointer()) return ptrType;

		if(CType.getUnitType().equals(cleanType)) {
			/* In Steensgaard, we set the default cell type of structure which mixed the 
			 * scalar type and pointer type is unit type (byte type) to enable byte-based
			 * encoding
			 */
			IOUtils.debug().pln("WARNING: mixed type. ");
			return mixType;
		}
		
		return valueType;
	}
}
