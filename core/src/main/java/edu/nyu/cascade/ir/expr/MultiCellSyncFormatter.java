package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import xtc.type.C;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

public class MultiCellSyncFormatter implements IRDataFormatter {

	private final ExpressionEncoding encoding;
	private final SyncValueType syncValueType;
  private final C cAnalyzer;
	
	private MultiCellSyncFormatter(ExpressionEncoding _encoding) {
		encoding = _encoding;
		syncValueType = SyncValueType.create(encoding, 
				encoding.getPointerEncoding().getType(), 
				encoding.getIntegerEncoding().getType());
		cAnalyzer = encoding.getCAnalyzer();
	}
	
	public static MultiCellSyncFormatter create(ExpressionEncoding encoding) {
		return new MultiCellSyncFormatter(encoding);
	}
	
	@Override
	public Type getAddressType() {
		return encoding.getPointerEncoding().getType();
	}

	@Override
	public Type getValueType() {
		return syncValueType.getType();
	}

	@Override
	public Type getSizeType() {
		return encoding.getPointerEncoding().getType().asTuple().getElementTypes().get(1);
	}

	@Override
	public int getSizeOfType(xtc.type.Type type) {
		return (int) cAnalyzer.getSize(type);
	}

	@Override
	public Expression getNullAddress() {
		return encoding.getPointerEncoding().getNullPtr();
	}

	@SuppressWarnings("unchecked")
  @Override
	public ArrayExpression updateMemoryArray(ArrayExpression memory, Expression index,
	    Expression value) {
		Preconditions.checkArgument(index.getNode() != null);
				
		if(value.isBoolean()) value = encoding.castToInteger(value);
		
		int size = (int) cAnalyzer.getSize(CType.getType(index.getNode()));	
		int wordSize = getWordSize();
		
		@SuppressWarnings("rawtypes")
    PointerEncoding ptrEncoding = encoding.getPointerEncoding();
		
		Expression idx = index;
		Type cellType = memory.getType().getElementType();
		
		for(int i = 0; i < size; i++) {
			if(i != 0)	idx = ptrEncoding.incr(idx);
			Expression valExpr = value.asBitVector().extract((i+1) * wordSize - 1, i * wordSize);
			Expression valuePrime = syncValueType.castExprToCell(valExpr, cellType);
			memory = memory.update(idx, valuePrime);
		}
		return memory;
	}

	@SuppressWarnings("unchecked")
  @Override
	public Expression indexMemoryArray(ArrayExpression memory, Expression index) {
		Preconditions.checkArgument(index.getNode() != null);
		
		int size = (int) cAnalyzer.getSize(CType.getType(index.getNode()));
		
		@SuppressWarnings("rawtypes")
    PointerEncoding ptrEncoding = encoding.getPointerEncoding();
		
		Expression res = syncValueType.castCellToExpr(memory.index(index), 
				CType.getType(index.getNode()));
		Expression idx = index;
		xtc.type.Type type = CType.getType(index.getNode());
		
		for(int i = 1; i < size; i++) {
			idx = ptrEncoding.incr(idx);
			Expression value = memory.index(idx);
			Expression valuePrime = syncValueType.castCellToExpr(value, type);
			res = valuePrime.asBitVector().concat(res);
		}
		return res;
	}

	@Override
	public Expression getUnknownValue(xtc.type.Type type) {
		int size = (int) cAnalyzer.getSize(type);
		int wordSize = encoding.getWordSize();
		ExpressionManager exprManager = encoding.getExpressionManager();
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
		return syncValueType.getValueType(type);
	}
	
	@Override
	public ArrayType getMemoryArrayType() {
		return encoding.getExpressionManager()
				.arrayType(getAddressType(), getValueType());
	}

	@Override
	public ArrayType getSizeArrayType() {
		return encoding.getExpressionManager()
				.arrayType(
						getAddressType().asTuple().getElementTypes().get(0), 
						getAddressType().asTuple().getElementTypes().get(1));
	}
	
	@Override
	public Expression getSizeZero() {
		return encoding.getPointerEncoding()
				.asSyncPointerEncoding().getOffsetEncoding().zero();
	}

	private int getWordSize() {
		return encoding.getWordSize();
	}

	@Override
	public ArrayExpression updateSizeArray(ArrayExpression sizeArr,
			Expression index, Expression value) {
		Preconditions.checkArgument(index.getType().equals(getAddressType()));
		Preconditions.checkArgument(index.isTuple());
		Expression indexRef = index.asTuple().index(0);
		return sizeArr.update(indexRef, value);
	}

	@Override
	public Expression indexSizeArray(ArrayExpression sizeArr, Expression index) {
		Preconditions.checkArgument(index.getType().equals(getAddressType()));
		Preconditions.checkArgument(index.isTuple());
		Expression indexRef = index.asTuple().index(0);
		return sizeArr.index(indexRef);
	}
	
	@Override
	public Expression getFreshPtr(String name, boolean fresh) {
		return encoding.getPointerEncoding().freshPtr(name, fresh);
	}
	
	@Override
	public Expression getBase(Expression ptr) {
		Preconditions.checkArgument(encoding.getPointerEncoding()
				.asSyncPointerEncoding().getBaseEncoding().isEncodingFor(ptr.getChild(0)));
		return ptr.getChild(0);
	}
}
