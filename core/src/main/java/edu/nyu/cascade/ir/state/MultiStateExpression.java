package edu.nyu.cascade.ir.state;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Identifiers;

public final class MultiStateExpression extends AbstractStateExpression {
	
	private final Map<String, SingleStateExpression> stateMap;
  private final Map<String, Object> properties = Maps.newHashMap();
  private final Map<String, BooleanExpression> preAsserts = Maps.newHashMap();
  private final Map<String, BooleanExpression> postAsserts = Maps.newHashMap();
  private BooleanExpression guard;
	private BooleanExpression constraint;
	
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
	public String toString() {
		StringBuilder sb = new StringBuilder().append(toStringShort());
		if(constraint != null) sb.append("constraint: ").append(constraint).append("\n");
		if(guard != null) sb.append("guard: ").append(guard);
		return sb.toString();
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

	@Override
	public boolean hasProperty(String label) {
		return properties.containsKey(label);
	}

	@Override
	public Object getProperty(String label) {
		Preconditions.checkArgument(hasProperty(label));
		return properties.get(label);
	}
	
	@Override
	public void setPreAssertion(String label, BooleanExpression assertion) {
		if(preAsserts.containsKey(label)) 
			assertion = preAsserts.get(label).and(assertion);
		preAsserts.put(label, assertion);
	}
	
	@Override
	public void setPostAssertion(String label, BooleanExpression assertion) {
		if(postAsserts.containsKey(label)) 
			assertion = postAsserts.get(label).and(assertion);
		postAsserts.put(label, assertion);
	}

	@Override
	public void setProperties(Map<String, Object> props) {
		properties.putAll(props);
	}

	@Override
	public Map<String, Object> getProperties() {
		return properties;
	}
	
	@Override
  public void setConstraint(BooleanExpression constraint) {
  	this.constraint = constraint;
  }
  
  @Override
  public void setGuard(BooleanExpression guard) {
  	this.guard = guard;
  }
  
  @Override
  public BooleanExpression getConstraint() {
  	return constraint;
  }
  
  @Override
  public boolean hasScope() {
  	return properties.containsKey(Identifiers.SCOPE);
  }

	@Override
	public void setScope(Scope _scope) {
		properties.put(Identifiers.SCOPE, _scope);
	}

	@Override
	public Scope getScope() {
		return (Scope) properties.get(Identifiers.SCOPE);
	}

	@Override
  public boolean hasSameType(StateExpression state) {
	  Set<String> thisKeys = stateMap.keySet();
	  Map<String, SingleStateExpression> thatStateMap = state.asMultiple().stateMap;
	  Set<String> thatKeys = thatStateMap.keySet();
	  
	  if(!Sets.difference(thisKeys, thatKeys).isEmpty()) return false;
	  
	  for(String key : thisKeys) {
	  	if(!stateMap.get(key).hasSameType(thatStateMap.get(key))) return false;
	  }
	  
	  return true;
  }

	@Override
  public Object setProperty(String key, Object val) {
	  return properties.put(key, val);
  }
	
	@Override
	public BooleanExpression getGuard() {
		return guard;
	}
	
	@Override
  public Type[] getElemTypes() {
		List<Type> res = Lists.newArrayList();
		for(SingleStateExpression singleState : stateMap.values()) {
			for(Type elemType : singleState.getElemTypes()) {
				res.add(elemType);
			}
		}
		return res.toArray(new Type[res.size()]);
	}
	
	@Override
	public Map<String, BooleanExpression> getPreAssertions() {
		return preAsserts;
	}

	@Override
	public Map<String, BooleanExpression> getPostAssertions() {
		return postAsserts;
	}

	Map<String, SingleStateExpression> getStateMap() {
		return stateMap;
	}
}
