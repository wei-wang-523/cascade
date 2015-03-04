package edu.nyu.cascade.ir.formatter;

import xtc.type.PointerT;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.PointerEncoding;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

public abstract class AbstractDataFormatter implements IRDataFormatter {
	protected static final String QF_IDX_NAME = "Cascade.idx";
	
	final ExpressionEncoding encoding;
	final ExpressionManager exprManager;
	final PointerEncoding<? extends Expression> ptrEncoding;
	
	public AbstractDataFormatter(ExpressionEncoding _encoding) {
		encoding = _encoding;
		exprManager = encoding.getExpressionManager();
		ptrEncoding = encoding.getPointerEncoding();
	}
	
	@Override
	public Type getAddressType() {
		return ptrEncoding.getType();
	}
	
	/**
	 * @param type is not used in multi-cell bit-vector formatter
	 */
	@Override
	public Type getArrayElemType(long width) {
		return getValueType();
	}
	
	@Override
	public ArrayType getMarkArrayType() {
		return exprManager.arrayType(getAddressType(), exprManager.booleanType());
	}
	
	@Override
	public Expression getNullAddress() {
		return ptrEncoding.getNullPtr();
	}
	
	@Override
  public Type getSizeType() {
		return ptrEncoding.getType();
  }

	@Override
	public Expression indexSizeArray(ArrayExpression sizeArr, Expression index) {
		return sizeArr.index(index);
	}
	
	@Override
	public ArrayExpression updateMemoryArray(ArrayExpression memory, 
			Expression index, xtc.type.Type idxType, 
			Expression value, xtc.type.Type valType) {
		boolean isUnsigned = valType != null && CType.isUnsigned(valType);
		value = castValue(value, idxType, !isUnsigned);
		
		switch(idxType.tag()) {
		case STRUCT:
			long size = encoding.getCTypeAnalyzer().getSize(idxType);
			return updateStructInMemoryArray(memory, index, value, size);
		default:
			return updateScalarInMem(memory, idxType, index, value);
		}
	}
	
	@Override
	public ArrayExpression updateStructInMemoryArray(ArrayExpression memory, 
			Expression index, Expression value, long size) {
		
		for(long i = 0; i < size; i++) {
			Expression offsetExpr = ptrEncoding.ofExpression(encoding.integerConstant(i));
			Expression fromIndex = encoding.pointerPlus(index, offsetExpr);
			Expression toIndex = encoding.pointerPlus(value, offsetExpr);
			memory = memory.update(fromIndex, memory.index(toIndex));
		}
		
		return memory;
	}
	
	@Override
	public ArrayExpression updateSizeArray(ArrayExpression sizeArr,
			Expression index, Expression value) {
		value = castToSize(value);
		return sizeArr.update(index, value);
	}
	
	@Override
	public ArrayType getMemoryArrayType() {
		return exprManager.arrayType(getAddressType(), getValueType());
	}

	@Override
	public ArrayType getSizeArrayType() {
		return exprManager.arrayType(getAddressType(), getSizeType());
	}
	
	@Override
	public Expression getFreshPtr(String name, boolean fresh) {
		return encoding.getPointerEncoding().freshPtr(name, fresh);
	}
	
	abstract protected ArrayExpression updateScalarInMem(ArrayExpression memory,
	xtc.type.Type idxType, Expression index, Expression value);

	/**
	 * Cast <code>value</code> to <code>targetType</code>
	 * @param value
	 * @param targetType 
	 * @param isSigned
	 * @return
	 */
	Expression castValue(Expression value, xtc.type.Type targetType, boolean isSigned) {		
		if(value.isBoolean()) value = encoding.castToInteger(value);
		
		if(value.isInteger()) return value;
		
		targetType = targetType.resolve();
		assert(!targetType.isVoid());
		
		CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
		int lhsSize = (int) cTypeAnalyzer.getWidth(
				CType.isScalar(targetType) ? targetType : PointerT.TO_VOID);
		value = encoding.castToInteger(value, lhsSize, isSigned);
		
		return value;
	}
}
