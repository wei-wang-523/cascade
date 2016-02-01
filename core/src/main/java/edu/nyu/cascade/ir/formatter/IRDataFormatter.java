package edu.nyu.cascade.ir.formatter;

import java.util.List;

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
	
	Type getArrayElemType(xtc.type.Type type);
	
	Expression getNullAddress();
	
	Expression getSizeZero();
	
	ArrayType getMemoryArrayType();
	
	ArrayType getSizeArrayType();
	
	ArrayType getMarkArrayType();
	
	ArrayExpression initializeZero(ArrayExpression memory, Expression lval,
			xtc.type.Type lType);
	
	ArrayExpression updateMemoryArray(ArrayExpression memory, 
			Expression index, xtc.type.Type idxType,
			Expression value, @Nullable xtc.type.Type valType);
	
	ArrayExpression initializeValues(ArrayExpression memory, Expression lval,
			xtc.type.Type lType, List<Expression> rvals, List<xtc.type.Type> rTypes);
	
	Expression indexMemoryArray(ArrayExpression memory, Expression index, xtc.type.Type idxType);
	
	ArrayExpression updateSizeArray(ArrayExpression sizeArr, Expression index, Expression value);
	
	Expression indexSizeArray(ArrayExpression sizeArr, Expression index);
	
	Expression getUnknownValue(xtc.type.Type type);
	
	Expression getFreshPtr(String regionName, boolean fresh);

	Expression castToSize(Expression value);
	
	BooleanExpression memorySet(ArrayExpression memory, 
			Expression region, Expression size, Expression value);
	
	BooleanExpression memoryCopy(ArrayExpression destMemory, ArrayExpression srcMemory,
			Expression destRegion, Expression srcRegion, Expression size);
}
