package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.Type;

public class SingleCellFormatter implements IRDataFormatter {

	private final ExpressionEncoding encoding;
	
	private SingleCellFormatter(ExpressionEncoding encoding) {
		this.encoding = encoding;
	}
	
	public static SingleCellFormatter create(ExpressionEncoding encoding) {
		return new SingleCellFormatter(encoding);
	}
	
	@Override
	public Type getAddressType() {
		return encoding.getIntegerEncoding().getType();
	}

	@Override
	public Type getValueType() {
		return encoding.getIntegerEncoding().getType();
	}

	@Override
	public Expression getNullAddress() {
		return encoding.zero();
	}
	
	@Override
	public int getSizeOfType(xtc.type.Type type) {
		return 1;
	}

	@Override
	public ArrayExpression updateMemoryArray(ArrayExpression memory, Expression index,
	    Expression value) {
		if(value.isBoolean()) value = encoding.castToInteger(value);
		if(!value.getType().equals(getValueType())) {
			if(getValueType().isBitVectorType())
				value = encoding.castToInteger(value, getValueType().asBitVectorType().getSize());				
		}
		return memory.update(index, value);
	}

	@Override
	public Expression indexMemoryArray(ArrayExpression memory, Expression index) {
		return memory.index(index);
	}

	/**
	 * @param type is not used in single cell formatter
	 */
	@Override
	public Expression getUnknownValue(xtc.type.Type type) {
		return encoding.getIntegerEncoding().unknown(getValueType());
	}
	
	@Override
  public Type getSizeType() {
	  return getValueType();
  }
	
	@Override
  public Expression addressOf(Expression expr) {
		Preconditions.checkArgument(expr.getNode() != null);
    CellKind kind = CType.getCellKind(CType.getType(expr.getNode()));
    switch(kind) {
    case STRUCTORUNION: 
    case ARRAY:   return expr;
    default:      return expr.getChild(1);
    }
	}

	@Override
	public Type getArrayElemType(xtc.type.Type type) {
	  switch(CType.getCellKind(type)) {
	  case SCALAR :
	  case BOOL :     return getValueType();
	  case ARRAY : 
	  case POINTER :  
	  case STRUCTORUNION : return getAddressType();
	  default:    throw new IllegalArgumentException("Unsupported type " + type);
	  }
	}
}
