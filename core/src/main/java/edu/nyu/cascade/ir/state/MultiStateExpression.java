package edu.nyu.cascade.ir.state;

import java.util.Map;
import java.util.Map.Entry;
import com.google.common.collect.Maps;

public final class MultiStateExpression extends AbstractStateExpression {
	
	private final Map<String, SingleStateExpression> stateMap;
	
  private MultiStateExpression(Map<String, SingleStateExpression> stateMap) {
  	this.stateMap = stateMap;
  }
  
  static MultiStateExpression create() {
		Map<String, SingleStateExpression> stateMap = Maps.newHashMap();
		return new MultiStateExpression(stateMap);
	}
	
  static MultiStateExpression create(
  		Map<String, SingleStateExpression> stateMap) {
		return new MultiStateExpression(stateMap);
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
		return false;
	}
	
	@Override
	public String toStringShort() {
		StringBuilder sb = new StringBuilder();
		for(Entry<String, SingleStateExpression> entry : stateMap.entrySet()) {
			sb.append(entry.getKey()).append(":")
				.append(entry.getValue().toStringShort()).append("\n");
		}
		return sb.toString();
	}

	Map<String, SingleStateExpression> getStateMap() {
		return stateMap;
	}
}
