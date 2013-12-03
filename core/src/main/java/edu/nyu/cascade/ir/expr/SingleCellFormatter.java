package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import xtc.type.C;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.Type;

public class SingleCellFormatter implements IRDataFormatter {

	private final ExpressionEncoding encoding;
	
	@SuppressWarnings("unused")
  private final C cAnalyzer;
	
	
	private SingleCellFormatter(ExpressionEncoding encoding) {
		this.encoding = encoding;
		cAnalyzer = encoding.getCAnalyzer();
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
	public Expression getSizeZero(xtc.type.Type type) {
		return encoding.zero();
	}

	@Override
	public ArrayExpression updateMemoryArray(ArrayExpression memory, Expression index,
	    Expression value) {
		return memory.update(index, value);
	}

	@Override
	public Expression indexMemoryArray(ArrayExpression memory, Expression index) {
		return memory.index(index);
	}

	@Override
	public Expression getUnknownValue(xtc.type.Type type) {
		Type valueType = encoding.getIntegerEncoding().getType();
		return encoding.getIntegerEncoding().unknown(valueType);
	}
	
	@Override
  public Type getIntegerType() {
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
