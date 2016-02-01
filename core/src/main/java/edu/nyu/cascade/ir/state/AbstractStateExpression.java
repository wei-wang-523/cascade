package edu.nyu.cascade.ir.state;
import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.ExpressionManager;


public abstract class AbstractStateExpression implements StateExpression {
	
	@Override
	public SingleStateExpression asSingle() {
		Preconditions.checkArgument(!isLambda());
		Preconditions.checkArgument(isSingle());
		return (SingleStateExpression) this;
	}
	
	@Override
	public SingleLambdaStateExpression asSingleLambda() {
		Preconditions.checkArgument(isLambda());
		Preconditions.checkArgument(isSingle());
		return (SingleLambdaStateExpression) this;
	}
	
	@Override
	public MultiStateExpression asMultiple() {
		Preconditions.checkArgument(!isLambda());
		Preconditions.checkArgument(isMultiple());
		return (MultiStateExpression) this;
	}
	
	@Override
	public MultiLambdaStateExpression asMultiLambda() {
		Preconditions.checkArgument(isLambda());
		Preconditions.checkArgument(isMultiple());
		return (MultiLambdaStateExpression) this;
	}
	
	@Override
	final public void addPreGuard(BooleanExpression preGuard) {
		BooleanExpression guard = getGuard();
		ExpressionManager exprManager = guard.getExpressionManager();
		BooleanExpression tt = exprManager.tt();
		if(preGuard.equals(tt)) return;
		guard = preGuard.ifThenElse(guard, exprManager.ff()).asBooleanExpression();
		setGuard(guard);
	}
	
	@Override
	final public void addGuard(BooleanExpression _guard) {
		BooleanExpression guard = getGuard();
		ExpressionManager exprManager = guard.getExpressionManager();
		BooleanExpression tt = exprManager.tt();
		if(!guard.equals(tt)) {
			guard = guard.ifThenElse(_guard, exprManager.ff()).asBooleanExpression();
		} else {
			guard = _guard;
		}
		setGuard(guard);
	}

	@Override
	final public void addConstraint(BooleanExpression _constraint) {
		if(_constraint == null) return;
		BooleanExpression constraint = getConstraint();
		if(constraint != null) {
			constraint = constraint.and(_constraint);
		} else {
			constraint = _constraint;
		}
		setConstraint(constraint);
	}
}
