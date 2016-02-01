package edu.nyu.cascade.ir.formatter;

import java.util.Collections;
import java.util.List;
import java.util.ListIterator;

import com.google.common.base.Preconditions;

import xtc.type.PointerT;
import xtc.type.StringReference;
import xtc.type.StructT;
import xtc.type.VariableT;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.PointerEncoding;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

public abstract class AbstractDataFormatter implements IRDataFormatter {
	protected static final String QF_IDX_NAME = "Cascade.idx";
	
	final ExpressionEncoding encoding;
	final ExpressionManager exprManager;
	final PointerEncoding<? extends Expression> ptrEncoding;
	
	public AbstractDataFormatter(ExpressionEncoding _encoding) {
		encoding = _encoding;
		exprManager = encoding.getExpressionManager();
		ptrEncoding = encoding.getPointerEncoding();
	}
	
	@Override
	public Type getAddressType() {
		return ptrEncoding.getType();
	}
	
	/**
	 * @param type is not used in multi-cell bit-vector formatter
	 */
	@Override
	public Type getArrayElemType(xtc.type.Type type) {
		return getValueType();
	}
	
	@Override
	public ArrayType getMarkArrayType() {
		return exprManager.arrayType(getAddressType(), exprManager.booleanType());
	}
	
	@Override
	public Expression getNullAddress() {
		return ptrEncoding.getNullPtr();
	}
	
	@Override
  public Type getSizeType() {
		return ptrEncoding.getType();
  }

	@Override
	public Expression indexSizeArray(ArrayExpression sizeArr, Expression index) {
		return sizeArr.index(index);
	}
	
	@Override
	public ArrayExpression updateMemoryArray(ArrayExpression memory, 
			Expression index, xtc.type.Type idxType, 
			Expression value, xtc.type.Type valType) {
		boolean isUnsigned = valType != null && CType.isUnsigned(valType);
		value = castValue(value, idxType, !isUnsigned);
		
		switch(idxType.tag()) {
		case STRUCT:
			return updateStructureInMem(memory, idxType.resolve().toStruct(), index, value);
		default:
			return updateScalarInMem(memory, idxType, index, value);
		}
	}
	
	@Override
	public ArrayExpression updateSizeArray(ArrayExpression sizeArr,
			Expression index, Expression value) {
		value = castToSize(value);
		return sizeArr.update(index, value);
	}
	
	@Override
	public ArrayType getMemoryArrayType() {
		return exprManager.arrayType(getAddressType(), getValueType());
	}

	@Override
	public ArrayType getSizeArrayType() {
		return exprManager.arrayType(getAddressType(), getSizeType());
	}
	
	@Override
	public Expression getFreshPtr(String name, boolean fresh) {
		return encoding.getPointerEncoding().freshPtr(name, fresh);
	}
	
	@Override
	public ArrayExpression initializeValues(ArrayExpression memory, 
			Expression lval, 
			xtc.type.Type lType, 
			List<Expression> rvals, 
			List<xtc.type.Type> rTypes) {
		Preconditions.checkArgument(rvals.size() == rTypes.size());
		return initialize(memory, lval, lType, rvals.listIterator(), rTypes.listIterator());
	}
	
	@Override
	public ArrayExpression initializeZero(ArrayExpression memory, 
			Expression lval, xtc.type.Type lType) {
		return initialize(memory, lval, lType, 
				Collections.<Expression>emptyList().listIterator(), 
				Collections.<xtc.type.Type>emptyList().listIterator());
	}
	
	abstract protected ArrayExpression updateScalarInMem(ArrayExpression memory,
	xtc.type.Type idxType, Expression index, Expression value) ;

	/**
	 * Update memory with type info <code>type</code>. If type is
	 * structure, update the each field from <code>value</code>
	 * to <code>index</code>. Otherwise, update <code>value</code>
	 * at <code>index</code>
	 * 
	 * @param memory
	 * @param structType
	 * @param index
	 * @param value
	 * @return
	 */
	protected ArrayExpression updateStructureInMem(ArrayExpression memory, 
			StructT structType, Expression index, Expression value) {
		CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
		long size = cTypeAnalyzer.getSize(structType);
		
		for(long i = 0; i < size; i++) {
			Expression offsetExpr = ptrEncoding.ofExpression(encoding.integerConstant(i));
			Expression fromIndex = encoding.pointerPlus(index, offsetExpr);
			Expression toIndex = encoding.pointerPlus(value, offsetExpr);
			memory = memory.update(fromIndex, memory.index(toIndex));
		}
		
		return memory;
	}

	/**
	 * Cast <code>value</code> to <code>targetType</code>
	 * @param value
	 * @param targetType 
	 * @param isSigned
	 * @return
	 */
	Expression castValue(Expression value, xtc.type.Type targetType, boolean isSigned) {		
		if(value.isBoolean()) value = encoding.castToInteger(value);
		
		if(value.isInteger()) return value;
		
		targetType = targetType.resolve();
		assert(!targetType.isVoid());
		
		CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
		int lhsSize = (int) cTypeAnalyzer.getWidth(
				CType.isScalar(targetType) ? targetType : PointerT.TO_VOID);
		value = encoding.castToInteger(value, lhsSize, isSigned);
		
		return value;
	}
	
	/**
	 * Initialize memory at index <code>lval</code> with <code>type</code> with a set of 
	 * values with iterator <code>rvalsItr</code>, and its type <code>rTypeItr</code>
	 * 
	 * @param memory
	 * @param lval
	 * @param lType
	 * @param rvalsItr
	 * @param rTypeItr
	 * @return
	 */
	ArrayExpression initialize(ArrayExpression memory, Expression lval, xtc.type.Type lType, 
			ListIterator<Expression> rvalsItr, ListIterator<xtc.type.Type> rTypeItr) {
		CType cTypeAnalyzer = encoding.getCTypeAnalyzer();
		
		lType = lType.resolve();
		
		if(lType.isArray()) {
			
			if(rvalsItr.hasNext()) {
				
				xtc.type.Type rType = rTypeItr.next();
				
				// Flat String literal to char[] if assign char[] to char[]
				if(rType.hasShape() && rType.getShape().isString()) {
					
					// should call next() before calling remove()
					rvalsItr.next();
					
					// remove current string literal and its type
					rvalsItr.remove(); 
					rTypeItr.remove();
					
					xtc.type.Type charType = rType.resolve().toArray().getType();
					String literal = ((StringReference) rType.getShape()).getLiteral();
					for(int i = literal.length()-1; i >= 0; i--) {
						char c = literal.charAt(i);
						Expression charConst = encoding.characterConstant(c);
						rvalsItr.add(charConst);
						rTypeItr.add(charType);
						rvalsItr.previous();
						rTypeItr.previous();
					}
				} else {
					// replace the iterator to the original place
					rTypeItr.previous();
				}
			}
			
			xtc.type.Type cellType = lType.toArray().getType();
			long cellSize = cTypeAnalyzer.getSize(cellType);
			for(int i = 0; i < lType.toArray().getLength(); i++) {
				long offset = i * cellSize;
				Expression offsetExpr = encoding.integerConstant(offset);
				Expression idxExpr = encoding.pointerPlus(lval, offsetExpr);
				memory = initialize(memory, idxExpr, cellType, rvalsItr, rTypeItr);
			}
			return memory;
		}
		
		if(lType.isStruct() && lType.toStruct().getMembers() != null) {
			for(VariableT elem : lType.toStruct().getMembers()) {
				long offset = cTypeAnalyzer.getOffset(lType.toStruct(), elem.getName());
				Expression offsetExpr = encoding.integerConstant(offset);
				Expression idxExpr = encoding.pointerPlus(lval, offsetExpr);
				memory = initialize(memory, idxExpr, elem, rvalsItr, rTypeItr);
			}
			return memory;
		}
		
		if(lType.isUnion()) {
			VariableT elem = lType.toUnion().getMember(0);
			return initialize(memory, lval, elem, rvalsItr, rTypeItr);
		}
		
		Expression rval = rvalsItr.hasNext() ? rvalsItr.next() : encoding.zero();
		boolean isUnsigned = rTypeItr.hasNext() ? CType.isUnsigned(rTypeItr.next()) : false;
		rval = castValue(rval, lType, !isUnsigned);
		return updateScalarInMem(memory, lType, lval, rval);
	}
}
