package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
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
	
	Type getIntegerType();
	
	Type getArrayElemType(xtc.type.Type type);
	
	Expression getNullAddress();
	
	Expression getValueZero(xtc.type.Type type);
	
	ArrayExpression updateMemoryArray(ArrayExpression memory, Expression index, Expression value);
	
	Expression indexMemoryArray(ArrayExpression memory, Expression index);
	
	Expression getUnknownValue(xtc.type.Type type);

	Expression addressOf(Expression expr);

}
