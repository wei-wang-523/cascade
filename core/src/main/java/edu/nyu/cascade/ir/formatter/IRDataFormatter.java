package edu.nyu.cascade.ir.formatter;

import javax.annotation.Nullable;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;


/**
 * Data format analyzer based on Rats
 * 
 * @author Wei
 *
 */

public interface IRDataFormatter {

	Type getAddressType();
	
	Type getValueType();
	
	Type getSizeType();
	
	Type getArrayElemType(long width);
	
	Expression getNullAddress();
	
	Expression getSizeZero();
	
	ArrayType getMemoryArrayType();
	
	ArrayType getSizeArrayType();
	
	ArrayType getMarkArrayType();
	
	ArrayExpression updateMemoryArray(ArrayExpression memory, 
			Expression index, xtc.type.Type idxType,
			Expression value, @Nullable xtc.type.Type valType);
	
	ArrayExpression updateStructInMemoryArray(ArrayExpression memory,
			Expression index, Expression value, long range);
	
	Expression indexMemoryArray(ArrayExpression memory, Expression index, xtc.type.Type idxType);
	
	ArrayExpression updateSizeArray(ArrayExpression sizeArr, Expression index, Expression value);
	
	Expression indexSizeArray(ArrayExpression sizeArr, Expression index);
	
	Expression getUnknownValue(xtc.type.Type type);
	
	Expression getFreshPtr(String regionName, boolean fresh);

	Expression castToSize(Expression value);
	
	BooleanExpression memorySet(ArrayExpression memory, 
			Expression region, Expression size, Expression value);
	
	BooleanExpression memorySet(ArrayExpression memory, 
			Expression region, Expression size, int value);
	
	BooleanExpression memoryCopy(ArrayExpression destMemory, ArrayExpression srcMemory,
			Expression destRegion, Expression srcRegion, Expression size);
}
