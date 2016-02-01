package edu.nyu.cascade.ir.formatter;

import com.google.common.base.Preconditions;

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

public final class SingleCellLinearIntegerFormatter extends AbstractDataFormatter {
	
	private SingleCellLinearIntegerFormatter(ExpressionEncoding encoding) {
		super(encoding);
	}
	
	public static SingleCellLinearIntegerFormatter create(ExpressionEncoding encoding) {
		return new SingleCellLinearIntegerFormatter(encoding);
	}

	@Override
	public Type getValueType() {
		return encoding.getExpressionManager().integerType();
	}
	
	@Override
	public Expression indexMemoryArray(ArrayExpression memory, Expression index, xtc.type.Type idxType) {
		return memory.index(index);
	}
	
	@Override
	public ArrayExpression updateSizeArray(ArrayExpression sizeArr,
			Expression index, Expression value) {
		return sizeArr.update(index, value);
	}
	
	@Override
	public Expression castToSize(Expression value) {
		Preconditions.checkArgument(value.isInteger());
		return value;
	}
	
	@Override
	public Expression getSizeZero() {
		return ptrEncoding.getType().asInteger().zero();
	}

	/**
	 * @param type is not used in single cell formatter
	 */
	@Override
	public Expression getUnknownValue(xtc.type.Type type) {
		return encoding.getIntegerEncoding().unknown();
	}

	@Override
	public Type getArrayElemType(xtc.type.Type type) {
		Preconditions.checkNotNull(type);
		xtc.type.Type cleanType = type.resolve();
		return cleanType.isPointer() || cleanType.isArray() || cleanType.isStruct() || cleanType.isUnion() ?
				getAddressType() : getValueType();
	}
	
  @Override
  protected ArrayExpression updateScalarInMem(ArrayExpression memory, xtc.type.Type idxType,
  		Expression index, Expression value) {
  	return memory.update(index, value);
  }

	@Override
  public BooleanExpression memorySet(ArrayExpression memory, Expression region,
      Expression size, Expression value) {
		// TODO: no idea how to break the value into char and concat them back as integer value
		return encoding.tt().asBooleanExpression();
  }
	
	@Override
  public BooleanExpression memoryCopy(ArrayExpression destMemory, ArrayExpression srcMemory,
  		Expression destRegion, Expression srcRegion, Expression size) {
		// TODO: no idea how to break the value into char and concat them back as integer value
		return encoding.tt().asBooleanExpression();
  }
}
