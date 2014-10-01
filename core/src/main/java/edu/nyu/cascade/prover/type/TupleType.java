package edu.nyu.cascade.prover.type;

import java.util.List;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TupleExpression;

public interface TupleType extends Type, ScalarType {
  List<? extends Type> getElementTypes();
  int size();
  String getName();
  
  Expression index(Expression tuple, int index);
  TupleExpression update(Expression tuple, int index, Expression value);
  
	@Override
	TupleExpression variable(String name, boolean fresh);
	
	@Override
	TupleExpression boundVar(String name, boolean fresh);
	
	@Override
	TupleExpression boundExpression(String name, int index, boolean fresh);
}
