package edu.nyu.cascade.ir.formatter;

import xtc.type.StructT;

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
		return encoding.getExpressionManager().bitVectorType(CType.BYTE_SIZE);
	}
	
  @Override
	public Expression indexMemoryArray(ArrayExpression memory, Expression index, xtc.type.Type idxType) {
		Preconditions.checkArgument(index.isBitVector());
		CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
		long valueSize = cTypeAnalyzer.getWidth(idxType);
		int elemSize = memory.getElementType().asBitVectorType().getSize();
		int size = (int) valueSize/elemSize;
		
		if(size == 1) return memory.index(index);
		
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
		int size = (int) cTypeAnalyzer.getWidth(type);
		return encoding.getIntegerEncoding().unknown(size);
	}
	
	/**
	 * @param type is not used in multi-cell bit-vector formatter
	 */
	@Override
	public Type getArrayElemType(xtc.type.Type type) {
		if(type.resolve().isArray()) type = type.resolve().toArray().getType();
		CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
		int size = (int) cTypeAnalyzer.getWidth(type);
		return encoding.getExpressionManager().bitVectorType(size);
	}

	@Override
	protected ArrayExpression updateScalarInMem(ArrayExpression memory, xtc.type.Type idxType,
			Expression index, Expression value) {
		Preconditions.checkArgument(!(idxType.isUnion() || idxType.isArray()));
		
		if(isSingleCell(memory, idxType)) return memory.update(index, value);
		
		int length = getCellLength(memory, value);
    int cellSize = memory.getElementType().asBitVectorType().getSize();
		
		for(int i = 0; i < length; i++) {
			Expression offExpr = ptrEncoding.ofExpression(encoding.integerConstant(i));
			Expression idxExpr = encoding.pointerPlus(index, offExpr);
			Expression valExpr = value.asBitVector().extract((i+1) * cellSize - 1, i * cellSize);
			memory = memory.update(idxExpr, valExpr);
		}
		return memory;
	}
	
	@Override
	protected ArrayExpression updateStructureInMem(ArrayExpression memory, 
			StructT structType, Expression index, Expression value) {
		throw new UnsupportedOperationException("vari-cell.updateStructureInMem");
	}

	private boolean isSingleCell(ArrayExpression memory, xtc.type.Type idxType) {
		int elemTypeSize = memory.getElementType().asBitVectorType().getSize();
		CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
		long indexSize = cTypeAnalyzer.getWidth(idxType);
		return elemTypeSize == indexSize;
	}

	private int getCellLength(ArrayExpression memory, Expression value) {
		int elemTypeSize = memory.getElementType().asBitVectorType().getSize();
		int valueSize = value.asBitVector().getSize();
		int cellLength = valueSize / elemTypeSize;
		assert cellLength > 0;
		return cellLength;
	}

	@Override
  public BooleanExpression memorySet(ArrayExpression memory, Expression region,
      Expression size, Expression value) {
	  // TODO Auto-generated method stub
		throw new UnsupportedOperationException("vari-cell.memorySet");
  }
	
	@Override
  public BooleanExpression memoryCopy(ArrayExpression destMemory, ArrayExpression srcMemory,
  		Expression region, Expression size, Expression value) {
	  // TODO Auto-generated method stub
		throw new UnsupportedOperationException("vari-cell.memoryCopy");
  }
}
