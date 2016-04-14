package edu.nyu.cascade.ir.formatter;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Preferences;

/**
 * Formatter for vari-cell heap encoding with linear pointer type
 * compute the size of the partitioned memory array's element type
 * based on the size of each xtc type
 * 
 * @author Wei
 *
 */

public class VariCellLinearFormatter extends AbstractDataFormatter {
	
	private VariCellLinearFormatter(ExpressionEncoding encoding) {
		super(encoding);
	}
	
	public static VariCellLinearFormatter create(ExpressionEncoding encoding) {
		Preconditions.checkArgument(Preferences.isSet(Preferences.OPTION_BYTE_BASED));
		return new VariCellLinearFormatter(encoding);
	}
	
	@Override
	public Type getValueType() {
		return encoding.getExpressionManager().bitVectorType(encoding.getCTypeAnalyzer().getByteSize());
	}
	
  @Override
	public Expression indexMemoryArray(ArrayExpression memory, Expression index, xtc.type.Type idxType) {
		Preconditions.checkArgument(index.isBitVector());
		int valueSize = (int) encoding.getCTypeAnalyzer().getWidth(idxType);
		int cellSize = memory.getElementType().asBitVectorType().getSize();
		
		int length = valueSize < cellSize ? 1 : getCellLength(memory, valueSize);
		if(length == 1) return memory.index(index);
		
		Expression res = null;
		for(int i = 0; i < length; i++) {
			Expression offExpr = ptrEncoding.ofExpression(encoding.integerConstant(i));
			Expression idxExpr = encoding.pointerPlus(index, offExpr);
			Expression value = memory.index(idxExpr);
			if(res == null)	res = value;
			else						res = value.asBitVector().concat(res);
		}
		return res;
	}
  
	@Override
	public Expression castToSize(Expression size) {
		// size is unsigned long
		return encoding.castToInteger(size, 
				getSizeType().asBitVectorType().getSize(), false);
	}
	
	@Override
	public Expression getSizeZero() {
		return getSizeType().asBitVectorType().constant(0);
	}

	@Override
	public Expression getUnknownValue(xtc.type.Type type) {
		CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
		int size = (int) cTypeAnalyzer.getWidth(type);
		return encoding.getIntegerEncoding().unknown(size);
	}
	
	/**
	 * @param type is not used in multi-cell bit-vector formatter
	 */
	@Override
	public Type getArrayElemType(long width) {
		Preconditions.checkArgument(width > 0);
		return encoding.getExpressionManager().bitVectorType((int) width);
	}

	@Override
	public BooleanExpression memorySet(ArrayExpression memory,
			Expression region, Expression size, Expression value) {
		int cellSize = memory.getType().getElementType().asBitVectorType().getSize();
		int byteSize = CType.getInstance().getByteSize();
		// Extract the the low 8 bit of value
		Expression valueToChar = encoding.castToInteger(value, byteSize);
		Expression valueInCellSize = null;
		for(int i = 0; i < cellSize/byteSize; ++i) {
			if(valueInCellSize == null)
				valueInCellSize = valueToChar;
			else
				valueInCellSize = valueToChar.asBitVector().concat(valueInCellSize);
		}
		
		Expression idxVar = getSizeType().asBitVectorType().boundVar(QF_IDX_NAME, true);
		Expression idxWithinRrange = encoding.and(
				encoding.greaterThanOrEqual(idxVar, getSizeZero()),
				encoding.lessThan(idxVar, size));
		Expression setToValue = memory.index(encoding.pointerPlus(region, idxVar)).eq(valueInCellSize);
		
		return encoding.forall(idxVar, 
				encoding.implies(idxWithinRrange, setToValue)).asBooleanExpression();
	}
	
	@Override
	public BooleanExpression memorySet(ArrayExpression memory,
			Expression region, Expression size, int value) {
		int cellSize = memory.getType().getElementType().asBitVectorType().getSize();
		int byteSize = CType.getInstance().getByteSize();
		while(cellSize >= byteSize) {
			byteSize += byteSize;
			value = value << byteSize + value;
		}
		
		Expression valueInCellSize = encoding.castToInteger(
				encoding.integerConstant(value), cellSize);
		Expression idxVar = getSizeType().asBitVectorType().boundVar(QF_IDX_NAME, true);
		Expression idxWithinRrange = encoding.and(
				encoding.greaterThanOrEqual(idxVar, getSizeZero()),
				encoding.lessThan(idxVar, size));
		Expression setToValue = memory.index(encoding.pointerPlus(region, idxVar)).eq(valueInCellSize);
		
		return encoding.forall(idxVar, 
				encoding.implies(idxWithinRrange, setToValue)).asBooleanExpression();
	}

	@Override
	public BooleanExpression memoryCopy(ArrayExpression destMemory, ArrayExpression srcMemory,
			Expression destRegion, Expression srcRegion, Expression size) {		
		Expression idxVar = getSizeType().asBitVectorType().boundVar(QF_IDX_NAME, true);
		Expression idxWithinRrange = encoding.and(
				encoding.greaterThanOrEqual(idxVar, getSizeZero()),
				encoding.lessThan(idxVar, size));
		
		Expression destValue = destMemory.index(encoding.pointerPlus(destRegion, idxVar));
		Expression srcValue = srcMemory.index(encoding.pointerPlus(srcRegion, idxVar));
		
		return encoding.forall(idxVar, 
				encoding.implies(idxWithinRrange, destValue.eq(srcValue))).asBooleanExpression();
	}

	@Override
	protected ArrayExpression updateScalarInMem(ArrayExpression memory, xtc.type.Type idxType,
			Expression index, Expression value) {
		Preconditions.checkArgument(!(idxType.isUnion() || idxType.isArray()));
		
		if(isSingleCell(memory, idxType)) return memory.update(index, value);
		
    int cellSize = memory.getElementType().asBitVectorType().getSize();
		int valueSize = value.asBitVector().getSize();
		if(valueSize < cellSize) {
			value = encoding.castToInteger(value, cellSize);
			valueSize = value.asBitVector().getSize();
		}
		
		int length = getCellLength(memory, valueSize);
		
		for(int i = 0; i < length; i++) {
			Expression offExpr = ptrEncoding.ofExpression(encoding.integerConstant(i));
			Expression idxExpr = encoding.pointerPlus(index, offExpr); 
			int high = (i+1) * cellSize - 1;
			int low = i * cellSize;
			Expression valExpr = value.asBitVector().extract(high, low);
			memory = memory.update(idxExpr, valExpr);
		}
		return memory;
	}

	private boolean isSingleCell(ArrayExpression memory, xtc.type.Type idxType) {
		int elemTypeSize = memory.getElementType().asBitVectorType().getSize();
		CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
		long indexSize = cTypeAnalyzer.getWidth(idxType);
		return elemTypeSize == indexSize;
	}

	private int getCellLength(ArrayExpression memory, int valueSize) {
		int elemTypeSize = memory.getElementType().asBitVectorType().getSize();
		int cellLength = valueSize / elemTypeSize;
		return cellLength;
	}
}
