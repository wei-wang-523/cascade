package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.UninterpretedExpression;

public interface UninterpretedType extends Type, ScalarType {
  String getName();
  
	@Override
	UninterpretedExpression variable(String name, boolean fresh);
	
	@Override
	UninterpretedExpression boundVar(String name, boolean fresh);
	
	@Override
	UninterpretedExpression boundExpression(String name, int index, boolean fresh);
}
