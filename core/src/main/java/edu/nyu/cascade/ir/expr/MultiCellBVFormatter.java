package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import xtc.type.C;
import xtc.type.IntegerT;
import xtc.type.PointerT;
import xtc.type.VoidT;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;

public class MultiCellBVFormatter implements IRDataFormatter {

	private final ExpressionEncoding encoding;
	private final ExpressionManager exprManager;
  private final C cAnalyzer;
	
	private MultiCellBVFormatter(ExpressionEncoding _encoding) {
		encoding = _encoding;
		exprManager = encoding.getExpressionManager();
		cAnalyzer = encoding.getCAnalyzer();
	}
	
	public static MultiCellBVFormatter create(ExpressionEncoding encoding) {
		return new MultiCellBVFormatter(encoding);
	}
	
	@Override
	public BitVectorType getAddressType() {
		int size = (int) cAnalyzer.getSize(new PointerT(new VoidT()));
		return exprManager.bitVectorType(size * getWordSize());
	}

	@Override
	public BitVectorType getValueType() {
		return exprManager.bitVectorType(getWordSize());
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
		int size = getAddressType().asBitVectorType().getSize();
		return exprManager.bitVectorZero(size);
	}

	@Override
	public ArrayExpression updateMemoryArray(ArrayExpression memory, Expression index,
	    Expression value) {
		Preconditions.checkArgument(index.getNode() != null);
		
		if(value.isBoolean()) value = encoding.castToInteger(value);
		
		int addrSize = getAddressType().getSize();		
		int size = (int) cAnalyzer.getSize(CType.getType(index.getNode()));	
		int wordSize = getWordSize();
		
		for(int i = 0; i < size; i++) {
			Expression offExpr = exprManager.bitVectorConstant(i, addrSize);
			Expression idxExpr = index.asBitVector().plus(addrSize, offExpr);
			Expression valExpr = value.asBitVector().extract((i+1) * wordSize - 1, i * wordSize);
			memory = memory.update(idxExpr, valExpr);
		}
		return memory;
	}

	@Override
	public Expression indexMemoryArray(ArrayExpression memory, Expression index) {
		Preconditions.checkArgument(index.getNode() != null);
		
		int addSize = getAddressType().getSize();
		int size = (int) cAnalyzer.getSize(CType.getType(index.getNode()));
		
		Expression res = memory.index(index);
		for(int i = 1; i < size; i++) {
			Expression offExpr = exprManager.bitVectorConstant(i, addSize);
			Expression idxExpr = index.asBitVector().plus(addSize, offExpr);
			Expression value = memory.index(idxExpr);
			res = value.asBitVector().concat(res);
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
}
