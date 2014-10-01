package edu.nyu.cascade.ir.memory.safety;

import edu.nyu.cascade.prover.Expression;

public interface PredicateClosure {
	Expression eval(Expression... args);
	Expression getBodyExpr();
	Expression[] getVars();
	Expression getUninterpretedFunc();
}
