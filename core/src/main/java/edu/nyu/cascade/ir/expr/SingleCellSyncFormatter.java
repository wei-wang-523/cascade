package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.CType.CellKind;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

/**
 * Formatter for single-cell heap encoding with synchronous pointer type
 * 
 * @author Wei
 *
 */

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
		Type valueType = getValueType();
		if(!value.getType().equals(valueType)) {
			if(valueType.isBitVectorType())
				value = encoding.castToInteger(value, valueType.asBitVectorType().getSize());				
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
		xtc.type.Type resolvedType = type.resolve();
		if(resolvedType.isArray() || resolvedType.isPointer())
			return encoding.getPointerEncoding().unknown();
		else
			return encoding.getIntegerEncoding().unknown(syncValueType.getValueType(type));
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
		return syncValueType.getValueType(type);
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
		Preconditions.checkArgument(index.isTuple());
		Expression indexRef = index.asTuple().index(0);
		return sizeArr.update(indexRef, value);
	}

	@Override
	public Expression indexSizeArray(ArrayExpression sizeArr, Expression index) {
		Preconditions.checkArgument(index.getType().equals(getAddressType()));
		Preconditions.checkArgument(index.isTuple());
		Expression indexRef = index.asTuple().index(0);
		return sizeArr.index(indexRef);
	}
	
	@Override
	public Expression getFreshPtr(String name, boolean fresh) {
		return encoding.getPointerEncoding().freshPtr(name, fresh);
	}
	
	@Override
	public Expression getBase(Expression ptr) {
		Preconditions.checkArgument(ptr.isTuple());
		return ptr.asTuple().getChild(0);
	}
}
