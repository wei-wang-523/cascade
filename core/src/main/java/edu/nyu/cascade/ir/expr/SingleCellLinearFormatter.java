package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

/**
 * Formatter for single-cell heap encoding with linear pointer type
 * 
 * @author Wei
 *
 */

public class SingleCellLinearFormatter implements IRDataFormatter {

	private final ExpressionEncoding encoding;
	
	private SingleCellLinearFormatter(ExpressionEncoding encoding) {
		this.encoding = encoding;
	}
	
	public static SingleCellLinearFormatter create(ExpressionEncoding encoding) {
		return new SingleCellLinearFormatter(encoding);
	}
	
	@Override
	public Type getAddressType() {
		return encoding.getPointerEncoding().getType();
	}

	@Override
	public Type getValueType() {
		return encoding.getIntegerEncoding().getType();
	}

	@Override
	public Expression getNullAddress() {
		return encoding.getPointerEncoding().getNullPtr();
	}
	
	@Override
	public int getSizeOfType(xtc.type.Type type) {
		return 1;
	}

	@Override
	public ArrayExpression updateMemoryArray(ArrayExpression memory, Expression index,
	    Expression value) {
		if(value.isBoolean()) value = encoding.castToInteger(value);
		if(!value.getType().equals(getValueType())) {
			if(getValueType().isBitVectorType())
				value = encoding.castToInteger(value, getValueType().asBitVectorType().getSize());				
		}
		return memory.update(index, value);
	}

	@Override
	public Expression indexMemoryArray(ArrayExpression memory, Expression index) {
		return memory.index(index);
	}

	/**
	 * @param type is not used in single cell formatter
	 */
	@Override
	public Expression getUnknownValue(xtc.type.Type type) {
		return encoding.getIntegerEncoding().unknown(getValueType());
	}
	
	@Override
  public Type getSizeType() {
	  return getValueType();
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

	@Override
	public Type getArrayElemType(xtc.type.Type type) {
	  switch(CType.getCellKind(type)) {
	  case SCALAR :
	  case BOOL :     return getValueType();
	  case ARRAY : 
	  case POINTER :  
	  case STRUCTORUNION : return getAddressType();
	  default:    throw new IllegalArgumentException("Unsupported type " + type);
	  }
	}
	
	@Override
	public ArrayType getMemoryArrayType() {
		return encoding.getExpressionManager()
				.arrayType(getAddressType(), getValueType());
	}

	@Override
	public ArrayType getSizeArrayType() {
		return encoding.getExpressionManager()
				.arrayType(getAddressType(), getSizeType());
	}

	@Override
	public Expression getSizeZero() {
		return encoding.getIntegerEncoding().zero();
//		return encoding.getExpressionManager()
//				.bitVectorZero(getSizeType().asBitVectorType().getSize());
	}
	
	@Override
	public ArrayExpression updateSizeArray(ArrayExpression sizeArr,
			Expression index, Expression value) {
		return sizeArr.update(index, value);
	}

	@Override
	public Expression indexSizeArray(ArrayExpression sizeArr, Expression index) {
		return sizeArr.index(index);
	}
	
	@Override
	public Expression getFreshPtr(String name, boolean fresh) {
		return encoding.getPointerEncoding().freshPtr(name, fresh);
	}
	
	@Override
	public Expression getBase(Expression ptr) {
		return ptr;
	}
}
