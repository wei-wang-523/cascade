package edu.nyu.cascade.ir.expr;

import xtc.tree.Node;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

public interface IRHeapEncoding {
	
	ArrayType getSizeArrType();
	
	ArrayType getMemoryType();

	Type getAddressType();
	
	Type getValueType();

	Type getArrayElemType(xtc.type.Type type);

	Expression freshAddress(String varName, IRVarInfo info, xtc.type.Type type);
	
	Expression freshRegion(String regionName, Node regionNode);
	
	ArrayExpression updateSizeArr(ArrayExpression sizeArr, Expression lval, Expression rval);
	
	Expression indexMemArr(ArrayExpression memArr, Expression lval);
	
	ArrayExpression updateMemArr(ArrayExpression memArr, Expression lval, Expression rval);
	
	ArrayExpression getConstSizeArr(ArrayType sizeArrType);
	
	Expression getValueZero();
	
	Expression getUnknownValue(xtc.type.Type type);
	
	Expression getNullAddress();
	
	Expression addressOf(Expression expr);
	
	MemoryVarSets getCategorizedVars(Iterable<IRVar> iterable);
	
	Expression getLastRegion();
	
	void updateLastRegion(Expression region);
	
	void updateLastRegion(String name, Expression region);
	
	Expression getLastRegion(String name);
	
	MemoryVarSets getMemVarSets();
	
	boolean isLinear();
	
	boolean isSync();
	
	LinearHeapEncoding castToLinear();
	
	SynchronousHeapEncoding castToSync();
	
}
