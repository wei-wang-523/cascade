package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import xtc.type.C;
import xtc.type.IntegerT;
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

public class MultiCellLinearBurstallSimpleFormatter implements IRDataFormatter {

	private final ExpressionEncoding encoding;
	private final ExpressionManager exprManager;
  private final C cAnalyzer;
	
	private MultiCellLinearBurstallSimpleFormatter(ExpressionEncoding _encoding) {
		encoding = _encoding;
		exprManager = encoding.getExpressionManager();
		cAnalyzer = encoding.getCAnalyzer();
	}
	
	public static MultiCellLinearBurstallSimpleFormatter create(ExpressionEncoding encoding) {
		return new MultiCellLinearBurstallSimpleFormatter(encoding);
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

  @Override
	public ArrayExpression updateMemoryArray(ArrayExpression memory, Expression index,
	    Expression value) {
		Preconditions.checkArgument(index.getNode() != null);
		
		if(value.isBoolean()) value = encoding.castToInteger(value);
		
		Type valueType = memory.getElementType();
		if(!value.getType().equals(valueType)) {
			if(valueType.isBitVectorType())
				value = encoding.castToInteger(value, valueType.asBitVectorType().getSize());				
		}
		return memory.update(index, value);
	}

  @Override
	public Expression indexMemoryArray(ArrayExpression memory, Expression index) {
		return memory.index(index);
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
		int size = (int) encoding.getCAnalyzer().getSize(type);
		int wordSize = encoding.getWordSize();
		return encoding.getExpressionManager().bitVectorType(wordSize * size);
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
