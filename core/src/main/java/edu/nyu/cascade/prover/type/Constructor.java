package edu.nyu.cascade.prover.type;

import com.google.common.collect.ImmutableList;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.InductiveExpression;

public interface Constructor {
	InductiveExpression apply(Expression... args);

	InductiveExpression apply(Iterable<? extends Expression> args);

	int getArity();

	ExpressionManager getExpressionManager();

	String getName();

	ImmutableList<? extends Selector> getSelectors();

	InductiveType getType();
}
