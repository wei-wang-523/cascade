package edu.nyu.cascade.ir.formatter;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.Type;

/**
 * Formatter for multi-cell heap encoding with linear pointer type
 * 
 * @author Wei
 *
 */

public final class MultiCellLinearFormatter extends AbstractDataFormatter {
	
	public MultiCellLinearFormatter(ExpressionEncoding encoding) {
		super(encoding);
	}

	public static MultiCellLinearFormatter create(ExpressionEncoding encoding) {
		return new MultiCellLinearFormatter(encoding);
	}
	
	@Override
	public Type getValueType() {
		return encoding.getExpressionManager().bitVectorType(encoding.getCTypeAnalyzer().getByteSize());
	}
  
  @Override
  protected ArrayExpression updateScalarInMem(ArrayExpression memory, xtc.type.Type idxType,
  		Expression index, Expression value) {
  	CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
		long size = cTypeAnalyzer.getSize(idxType);
		int cellSize = memory.getType().getElementType().asBitVectorType().getSize();
		for(int i = 0; i < size; i++) {
			Expression offExpr = ptrEncoding.ofExpression(encoding.integerConstant(i));
			Expression idxExpr = encoding.pointerPlus(index, offExpr);
			int high = (i+1) * cellSize - 1;
			int low = i * cellSize;
			Expression valExpr = value.asBitVector().extract(high, low);
			memory = memory.update(idxExpr, valExpr);
		}
		
		return memory;
  }
  
  @Override
	public Expression indexMemoryArray(ArrayExpression memory, Expression index, xtc.type.Type idxType) {
  	CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
		long size = cTypeAnalyzer.getSize(idxType);
		
		Expression res = null;
		for(int i = 0; i < size; i++) {
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
		return encoding.castToInteger(size, getSizeType().asBitVectorType().getSize());
	}
	
	@Override
	public Expression getSizeZero() {
		return getSizeType().asBitVectorType().constant(0);
	}

	@Override
	public Expression getUnknownValue(xtc.type.Type type) {
		CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
		long size = cTypeAnalyzer.getWidth(type);
		return encoding.getIntegerEncoding().unknown(size);
	}
	
	@Override
	public BooleanExpression memorySet(ArrayExpression memory,
			Expression region, Expression size, Expression value) {
		int cellSize = memory.getType().getElementType().asBitVectorType().getSize();
		
		// Extract the the low 8 bit of value
		Expression valueToChar = encoding.castToInteger(value, cellSize);
		
		Expression idxVar = getSizeType().asBitVectorType().boundVar(QF_IDX_NAME, true);
		Expression idxWithinRrange = encoding.and(
				encoding.greaterThanOrEqual(idxVar, getSizeZero()),
				encoding.lessThan(idxVar, size));
		Expression setToValue = memory.index(encoding.pointerPlus(region, idxVar)).eq(valueToChar);
		
		return encoding.forall(idxVar, 
				encoding.implies(idxWithinRrange, setToValue)).asBooleanExpression();
	}

	@Override
	public BooleanExpression memorySet(ArrayExpression memory,
			Expression region, Expression size, int value) {
		int cellSize = memory.getType().getElementType().asBitVectorType().getSize();
		
		// Extract the the low 8 bit of value
		Expression valueToChar = encoding.castToInteger(encoding.integerConstant(value), cellSize);
		
		Expression idxVar = getSizeType().asBitVectorType().boundVar(QF_IDX_NAME, true);
		Expression idxWithinRrange = encoding.and(
				encoding.greaterThanOrEqual(idxVar, getSizeZero()),
				encoding.lessThan(idxVar, size));
		Expression setToValue = memory.index(encoding.pointerPlus(region, idxVar)).eq(valueToChar);
		
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
}
