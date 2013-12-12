package edu.nyu.cascade.ir.expr;

import xtc.tree.Node;

import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.Type;

public interface IRHeapEncoding {

	ArrayType getMemoryType() ;

	ArrayType getSizeArrType() ;

	Type getAddressType() ;

	Type getValueType() ;
	
	Type getSizeType() ;
	
	Expression getSizeZero() ;
	
	Expression getNullAddress() ;

	Type getArrayElemType(xtc.type.Type type) ;
	
	ArrayExpression updateMemArr(ArrayExpression memArr, Expression lval,
	    Expression rval) ;
	
	Expression indexMemArr(ArrayExpression memArr, Expression lval) ;
	
	ArrayExpression updateSizeArr(ArrayExpression sizeArr, Expression lval,
	    Expression rval) ;

	ArrayExpression getConstSizeArr(ArrayType sizeArrType) ;

	Expression freshAddress(String varName, IRVarInfo info, xtc.type.Type type) ;

	Expression freshRegion(String regionName, Node regionNode) ;

	MemoryVarSets getCategorizedVars(Iterable<IRVar> equivVars) ;
	
	Expression getUnknownValue(xtc.type.Type type) ;
	
	Expression getLastRegion() ;

  Expression getLastRegion(String name) ;

	void updateLastRegion(Expression region) ;
	
	void updateLastRegion(String name, Expression region) ;
	
	MemoryVarSets getMemVarSets() ;

	ExpressionManager getExpressionManager() ;
	
	ExpressionEncoding getExpressionEncoding() ;
	
	IRDataFormatter getDataFormatter() ;
	
	int getSizeOfVar(Expression stackVar) ;
  Expression addressOf(Expression expr) ;
}
