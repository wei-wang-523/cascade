package edu.nyu.cascade.ir.formatter;

import com.google.common.base.Preconditions;

import xtc.type.IntegerT;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.PointerEncoding;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;

/**
 * Formatter for vari-cell heap encoding with linear pointer type
 * compute the size of the partitioned memory array's element type
 * based on the size of each xtc type
 * 
 * @author Wei
 *
 */

public class VariCellLinearFormatter implements IRDataFormatter {

	private final ExpressionEncoding encoding;
	private final ExpressionManager exprManager;
	
	private VariCellLinearFormatter(ExpressionEncoding _encoding) {
		encoding = _encoding;
		exprManager = encoding.getExpressionManager();
	}
	
	public static VariCellLinearFormatter create(ExpressionEncoding encoding) {
		return new VariCellLinearFormatter(encoding);
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
	public BitVectorType getSizeType() {
		long size = CType.getSizeofType(IntegerT.LONG);
		int wordSize = encoding.getWordSize();
	  return exprManager.bitVectorType((int) (size * wordSize));
	}

	@Override
	public Expression getNullAddress() {
			return encoding.getPointerEncoding().getNullPtr();
	}

  @SuppressWarnings("unchecked")
  @Override
	public ArrayExpression updateMemoryArray(ArrayExpression memory, Expression index,
	    Expression value) {
		Preconditions.checkNotNull(index.getNode());
		
		if(value.isBoolean()) value = encoding.castToInteger(value);
		
		int lhsSize = (int) CType.getSizeofType(CType.getType(index.getNode())) 
				* encoding.getWordSize();
		int rhsSize = value.asBitVector().getSize();
		
		if(rhsSize < lhsSize) {
	    /* For any assignment a = b;, the value of b is converted to a value of the type of a, 
	     * provided that is possible, and that converted value is assigned to a.
	     */
			value = encoding.castToInteger(value, lhsSize);
		}
		
		int cellSize = memory.getElementType().asBitVectorType().getSize();
		
		if(lhsSize == cellSize) return memory.update(index, value); // not collapse
		
    @SuppressWarnings("rawtypes")
    PointerEncoding ptrEncoding = encoding.getPointerEncoding();
    
		int size = lhsSize/cellSize; assert(size > 0);
    
		Expression idx = index;
		for(int i = 0; i < size; i++, idx = ptrEncoding.incr(idx)) {
			Expression valExpr = value.asBitVector().extract((i+1) * cellSize - 1, i * cellSize);
			memory = memory.update(idx, valExpr);
		}
		return memory;
	}

  @SuppressWarnings("unchecked")
  @Override
	public Expression indexMemoryArray(ArrayExpression memory, Expression index) {
		Preconditions.checkNotNull(index.getNode());
		Preconditions.checkArgument(index.isBitVector());
		long valueSize = CType.getSizeofType(CType.getType(index.getNode()))
				* encoding.getWordSize();
		int elemSize = memory.getType().getElementType().asBitVectorType().getSize();
		int size = (int) valueSize/elemSize;
		assert(size > 0);
		
		if(size == 1) return memory.index(index);
		
		@SuppressWarnings("rawtypes")
    PointerEncoding ptrEncoding = encoding.getPointerEncoding();
		
		Expression res = null, idx = index;
		for(int i = 0; i < size; i++, idx = ptrEncoding.incr(idx.asBitVector())) {
			Expression value = memory.index(idx);
			if(res == null)	res = value;
			else						res = value.asBitVector().concat(res);
		}
		return res;
	}

	@Override
	public Expression getUnknownValue(xtc.type.Type type) {
		int size = (int) CType.getSizeofType(type);
		int wordSize = encoding.getWordSize();
		Type valueType = exprManager.bitVectorType(size * wordSize);
		return encoding.getIntegerEncoding().unknown(valueType);
	}
	
	/**
	 * @param type is not used in multi-cell bit-vector formatter
	 */
	@Override
	public Type getArrayElemType(xtc.type.Type type) {
		if(type.resolve().isArray()) type = type.resolve().toArray().getType();
		long size = CType.getSizeofType(type);
		int wordSize = encoding.getWordSize();
		return encoding.getExpressionManager().bitVectorType((int) (wordSize * size));
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
		return encoding.getExpressionManager()
				.bitVectorZero(getSizeType().asBitVectorType().getSize());
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
		Preconditions.checkNotNull(index.getNode());
		
		if(value.isBoolean()) value = encoding.castToInteger(value);
		
		int lhsSize = (int) CType.getSizeofType(CType.getType(index.getNode())) 
				* encoding.getWordSize();
		int rhsSize = value.asBitVector().getSize();
		
		if(rhsSize < lhsSize) {
	    /* For any assignment a = b;, the value of b is converted to a value of the type of a, 
	     * provided that is possible, and that converted value is assigned to a.
	     */
			value = encoding.castToInteger(value, lhsSize);
		}
		
		return value;
	}
}
