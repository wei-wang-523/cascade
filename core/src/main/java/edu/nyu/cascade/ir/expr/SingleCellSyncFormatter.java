package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

public class SingleCellSyncFormatter implements IRDataFormatter {

	private final ExpressionEncoding encoding;
	private final SyncValueType syncValueType;
	
	private SingleCellSyncFormatter(ExpressionEncoding encoding) {
		this.encoding = encoding;
		syncValueType = SyncValueType.create(encoding, 
				encoding.getPointerEncoding().getType(), 
				encoding.getIntegerEncoding().getType());
	}
	
	public static SingleCellSyncFormatter create(ExpressionEncoding encoding) {
		return new SingleCellSyncFormatter(encoding);
	}
	
	@Override
	public Type getAddressType() {
		return encoding.getPointerEncoding().getType();
	}

	@Override
	public Type getValueType() {
		return syncValueType.getType();
//		return encoding.getIntegerEncoding().getType();
	}

	@Override
	public Expression getNullAddress() {
		return encoding.getPointerEncoding().getNullPtr();
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
		Type cellType = memory.getType().getElementType();
		Expression valuePrime = syncValueType.castExprToCell(value, cellType);
		return memory.update(index, valuePrime);
	}

	@Override
	public Expression indexMemoryArray(ArrayExpression memory, Expression index) {
		Expression value = memory.index(index);
		xtc.type.Type type = CType.getType(index.getNode());
		return syncValueType.castCellToExpr(value, type);
	}

	/**
	 * @param type is not used in single cell formatter
	 */
	@Override
	public Expression getUnknownValue(xtc.type.Type type) {
		return encoding.getIntegerEncoding().unknown(syncValueType.getValueType(type));
//		return encoding.getIntegerEncoding().unknown(getValueType());
	}
	
	@Override
  public Type getSizeType() {
	  return encoding.getPointerEncoding().getType().asTuple().getElementTypes().get(1);
  }
	
	@Override
  public Expression addressOf(Expression expr) {
		Preconditions.checkArgument(expr.getNode() != null);
    CellKind kind = CType.getCellKind(CType.getType(expr.getNode()));
    switch(kind) {
    case STRUCTORUNION: 
    case ARRAY:   
    	return expr;
    default:      
    	return expr.getChild(1);
    }
	}

	@Override
	public Type getArrayElemType(xtc.type.Type type) {
	  switch(CType.getCellKind(type)) {
	  case SCALAR :
	  case BOOL :
	  	return getValueType();
	  case ARRAY : 
	  case POINTER :
	  case STRUCTORUNION :
	  	return getAddressType();
	  default:    throw new IllegalArgumentException("Unsupported type " + type);
	  }
	}
	
	@Override
	public ArrayType getMemoryArrayType() {
		return encoding.getExpressionManager()
				.arrayType(getAddressType(), getValueType());
	}

	@Override
	public ArrayType getSizeArrayType() {
		return encoding.getExpressionManager()
				.arrayType(
						getAddressType().asTuple().getElementTypes().get(0), 
						getAddressType().asTuple().getElementTypes().get(1));
	}

	@Override
	public Expression getSizeZero() {
		return encoding.getPointerEncoding()
				.asSyncPointerEncoding().getOffsetEncoding().zero();
	}
	
	@Override
	public ArrayExpression updateSizeArray(ArrayExpression sizeArr,
			Expression index, Expression value) {
		Preconditions.checkArgument(index.getType().equals(getAddressType()));
		Expression indexRef = index.asTuple().getChild(0);
		return sizeArr.update(indexRef, value);
	}

	@Override
	public Expression indexSizeArray(ArrayExpression sizeArr, Expression index) {
		Preconditions.checkArgument(index.getType().equals(getAddressType()));
		Expression indexRef = index.asTuple().getChild(0);
		return sizeArr.index(indexRef);
	}
}
