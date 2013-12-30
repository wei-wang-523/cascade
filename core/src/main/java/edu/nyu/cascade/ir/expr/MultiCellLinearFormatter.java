package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import xtc.type.C;
import xtc.type.IntegerT;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;

/**
 * Formatter for multi-cell heap encoding with linear pointer type
 * 
 * @author Wei
 *
 */

public class MultiCellLinearFormatter implements IRDataFormatter {

	private final ExpressionEncoding encoding;
	private final ExpressionManager exprManager;
  private final C cAnalyzer;
	
	private MultiCellLinearFormatter(ExpressionEncoding _encoding) {
		encoding = _encoding;
		exprManager = encoding.getExpressionManager();
		cAnalyzer = encoding.getCAnalyzer();
	}
	
	public static MultiCellLinearFormatter create(ExpressionEncoding encoding) {
		return new MultiCellLinearFormatter(encoding);
	}
	
	@Override
	public Type getAddressType() {
//		int size = (int) cAnalyzer.getSize(new PointerT(new VoidT()));
//		return exprManager.bitVectorType(size * getWordSize());
		return encoding.getPointerEncoding().getType();
	}

	@Override
	public Type getValueType() {
//		return exprManager.bitVectorType(getWordSize());
		return encoding.getIntegerEncoding().getType();
	}

	@Override
	public BitVectorType getSizeType() {
		int size = (int) cAnalyzer.getSize(IntegerT.INT);
		int wordSize = encoding.getWordSize();
	  return exprManager.bitVectorType(size * wordSize);
	}

	@Override
	public int getSizeOfType(xtc.type.Type type) {
		return (int) cAnalyzer.getSize(type);
	}

	@Override
	public Expression getNullAddress() {
//		Type addrType = getAddressType();
//		if(addrType.isBitVectorType())
//			return exprManager.bitVectorZero(addrType.asBitVectorType().getSize());
//		else
			return encoding.getPointerEncoding().getNullPtr();
	}

  @SuppressWarnings("unchecked")
  @Override
	public ArrayExpression updateMemoryArray(ArrayExpression memory, Expression index,
	    Expression value) {
  	Preconditions.checkNotNull(index.getNode());
		
		if(value.isBoolean()) value = encoding.castToInteger(value);
		
		int size = (int) cAnalyzer.getSize(CType.getType(index.getNode()));	
		int wordSize = getWordSize();
		
    @SuppressWarnings("rawtypes")
    PointerEncoding ptrEncoding = encoding.getPointerEncoding();
    
		Expression idx = index;
		for(int i = 0; i < size; i++, idx = ptrEncoding.incr(idx)) {
			Expression valExpr = value.asBitVector().extract((i+1) * wordSize - 1, i * wordSize);
			memory = memory.update(idx, valExpr);
		}
		return memory;
	}

	@SuppressWarnings("unchecked")
  @Override
	public Expression indexMemoryArray(ArrayExpression memory, Expression index) {
		Preconditions.checkNotNull(index.getNode());
		
		int size = (int) cAnalyzer.getSize(CType.getType(index.getNode()));
		
		@SuppressWarnings("rawtypes")
    PointerEncoding ptrEncoding = encoding.getPointerEncoding();
		
		Expression res = null, idx = index;
		for(int i = 0; i < size; i++, idx = ptrEncoding.incr(idx)) {
			Expression value = memory.index(idx);
			if(res == null)	res = value;
			else						res = value.asBitVector().concat(res);
		}
		return res;
	}

	@Override
	public Expression getUnknownValue(xtc.type.Type type) {
		int size = (int) cAnalyzer.getSize(type);
		int wordSize = encoding.getWordSize();
		Type valueType = exprManager.bitVectorType(size * wordSize);
		return encoding.getIntegerEncoding().unknown(valueType);
	}

	@Override
  public Expression addressOf(Expression expr) {
		throw new UnsupportedOperationException("Multi-cell encoding doesn't support addressOf operation");
	}
	
	/**
	 * @param type is not used in multi-cell bit-vector formatter
	 */
	@Override
	public Type getArrayElemType(xtc.type.Type type) {
		return getValueType();
	}

	private int getWordSize() {
		return encoding.getWordSize();
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
}
