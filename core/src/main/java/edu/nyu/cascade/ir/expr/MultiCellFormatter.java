package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import xtc.type.C;
import xtc.type.IntegerT;
import xtc.type.PointerT;
import xtc.type.VoidT;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;

public class MultiCellFormatter implements IRDataFormatter {

	private final ExpressionEncoding encoding;
	private final ExpressionManager exprManager;
  private final C cAnalyzer;
	
	
	private MultiCellFormatter(ExpressionEncoding _encoding) {
		encoding = _encoding;
		exprManager = encoding.getExpressionManager();
		cAnalyzer = encoding.getCAnalyzer();
	}
	
	public static MultiCellFormatter create(ExpressionEncoding encoding) {
		return new MultiCellFormatter(encoding);
	}
	
	@Override
	public Type getAddressType() {
		int size = (int) cAnalyzer.getSize(new PointerT(new VoidT()));
		int cellSize = encoding.getCellSize();
		return exprManager.bitVectorType(size * cellSize);
	}

	@Override
	public Type getValueType() {
		int cellSize = encoding.getCellSize();
		return exprManager.bitVectorType(cellSize);
	}

	@Override
	public Expression getNullAddress() {
		int size = (int) cAnalyzer.getSize(new PointerT(new VoidT()));
		int cellSize = encoding.getCellSize();
		return exprManager.bitVectorZero(size * cellSize);
	}

	@Override
	public Expression getValueZero(xtc.type.Type type) {
		return encoding.zero();
	}

	@Override
	public ArrayExpression updateMemoryArray(ArrayExpression memory, Expression index,
	    Expression value) {
		Preconditions.checkArgument(index.getNode() != null);
		int size = (int) cAnalyzer.getSize(CType.getType(index.getNode()));
		int addSize = getAddressType().asBitVectorType().getSize();
		int cellSize = encoding.getCellSize();
		
		for(int i = 0; i < size; i++) {
			Expression offExpr = exprManager.bitVectorConstant(i, addSize);
			Expression idxExpr = index.asBitVector().plus(addSize, offExpr);
			Expression valExpr = value.asBitVector().extract((i+1) * cellSize - 1, i * cellSize);
			memory = memory.update(idxExpr, valExpr);
		}
		return memory;
	}

	@Override
	public Expression indexMemoryArray(ArrayExpression memory, Expression index) {
		Preconditions.checkArgument(index.getNode() != null);
		int size = (int) cAnalyzer.getSize(CType.getType(index.getNode()));
		int addSize = getAddressType().asBitVectorType().getSize();
		
		Expression res = memory.index(index);
		for(int i = 1; i < size; i++) {
			Expression offExpr = exprManager.bitVectorConstant(i, addSize);
			Expression idxExpr = index.asBitVector().plus(addSize, offExpr);
			Expression value = memory.index(idxExpr);
			res = res.asBitVector().concat(value);
		}
		return res;
	}

	@Override
	public Expression getUnknownValue(xtc.type.Type type) {
		int size = (int) cAnalyzer.getSize(type);
		int cellSize = encoding.getCellSize();
		Type valueType = exprManager.bitVectorType(size * cellSize);
		return encoding.getIntegerEncoding().unknown(valueType);
	}

	@Override
  public Type getIntegerType() {
		int size = (int) cAnalyzer.getSize(IntegerT.INT);
		int cellSize = encoding.getCellSize();
	  return exprManager.bitVectorType(size * cellSize);
  }
	
	@Override
  public Expression addressOf(Expression expr) {
		throw new UnsupportedOperationException("Multi-cell encoding doesn't support addressOf operation");
	}
	
	@Override
	public Type getArrayElemType(xtc.type.Type type) {
		return getValueType();
	}
}
