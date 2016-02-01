package edu.nyu.cascade.ir.formatter;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.ir.expr.ExpressionEncoding;
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
	public Type getArrayElemType(xtc.type.Type type) {
		Preconditions.checkNotNull(type);
		xtc.type.Type cleanType = type.resolve();
		return cleanType.isPointer() || cleanType.isArray() ? 
				getAddressType() : getValueType();
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

	@Override
	public Expression cast(Expression index, Expression value) {
		if(value.isBoolean()) value = encoding.castToInteger(value);
		if(!value.getType().equals(getValueType())) {
			if(getValueType().isBitVectorType())
				value = encoding.castToInteger(value, getValueType().asBitVectorType().getSize());				
		}
		
		return value;
	}
}
