package edu.nyu.cascade.ir.formatter;

import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.Type;

/**
 * Formatter for single-cell heap encoding with linear pointer type
 * 
 * @author Wei
 *
 */

public final class SingleCellLinearFormatter extends AbstractDataFormatter {

	private SingleCellLinearFormatter(ExpressionEncoding encoding) {
		super(encoding);
	}

	public static SingleCellLinearFormatter create(ExpressionEncoding encoding) {
		return new SingleCellLinearFormatter(encoding);
	}

	@Override
	public Type getValueType() {
		return encoding.getExpressionManager().bitVectorType(encoding
		    .getCTypeAnalyzer().getWordSize());
	}

	@Override
	public Expression castToSize(Expression size) {
		return encoding.castToInteger(size, getSizeType().asBitVectorType()
		    .getSize());
	}

	@Override
	public Expression indexMemoryArray(ArrayExpression memory, Expression index,
	    xtc.type.Type idxType) {
		return memory.index(index);
	}

	@Override
	public Expression getSizeZero() {
		return getSizeType().asBitVectorType().constant(0);
	}

	/**
	 * @param type
	 *          is not used in single cell formatter
	 */
	@Override
	public Expression getUnknownValue(xtc.type.Type type) {
		int size = getValueType().asBitVectorType().getSize();
		return encoding.getIntegerEncoding().unknown(size);
	}

	@Override
	public Type getArrayElemType(long width) {
		if (encoding.getCTypeAnalyzer().getWordSize() == width)
			return getValueType();
		else
			return getAddressType();
	}

	@Override
	protected ArrayExpression updateScalarInMem(ArrayExpression memory,
	    xtc.type.Type idxType, Expression index, Expression value) {
		return memory.update(index, value);
	}

	@Override
	public BooleanExpression memorySet(ArrayExpression memory, Expression region,
	    Expression size, Expression value) {
		// FIXME: single cell linear format is unsound for memory set
		return encoding.tt().asBooleanExpression();
	}

	@Override
	public BooleanExpression memorySet(ArrayExpression memory, Expression region,
	    Expression size, int value) {
		// FIXME: single cell linear format is unsound for memory set
		return encoding.tt().asBooleanExpression();
	}

	@Override
	public BooleanExpression memoryCopy(ArrayExpression destMemory,
	    ArrayExpression srcMemory, Expression destRegion, Expression srcRegion,
	    Expression size) {
		// FIXME: single cell linear format is unsound for memory copy
		return encoding.tt().asBooleanExpression();
	}
}
