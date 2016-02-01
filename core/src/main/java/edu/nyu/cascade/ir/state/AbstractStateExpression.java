package edu.nyu.cascade.ir.state;
import com.google.common.base.Preconditions;


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
}
