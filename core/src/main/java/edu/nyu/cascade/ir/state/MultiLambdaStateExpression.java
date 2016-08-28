package edu.nyu.cascade.ir.state;

import java.util.Map;
import java.util.Map.Entry;
import com.google.common.collect.Maps;

public final class MultiLambdaStateExpression extends AbstractStateExpression {
	private final Map<String, SingleLambdaStateExpression> stateMap;

	private MultiLambdaStateExpression(
			Map<String, SingleLambdaStateExpression> stateMap) {
		this.stateMap = stateMap;
	}

	public static MultiLambdaStateExpression create() {
		return create(Maps.<String, SingleLambdaStateExpression> newHashMap());
	}

	static MultiLambdaStateExpression create(
			Map<String, SingleLambdaStateExpression> stateMap) {
		return new MultiLambdaStateExpression(stateMap);
	}

	@Override
	public boolean isSingle() {
		return false;
	}

	@Override
	public boolean isMultiple() {
		return true;
	}

	@Override
	public boolean isLambda() {
		return true;
	}

	@Override
	public String toStringShort() {
		StringBuilder sb = new StringBuilder();
		for (Entry<String, SingleLambdaStateExpression> entry : stateMap
				.entrySet()) {
			sb.append(entry.getKey()).append(":")
					.append(entry.getValue().toStringShort()).append("\n");
		}
		return sb.toString();
	}

	Map<String, SingleLambdaStateExpression> getStateMap() {
		return stateMap;
	}
}
