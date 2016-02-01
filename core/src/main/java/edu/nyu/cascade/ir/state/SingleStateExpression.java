package edu.nyu.cascade.ir.state;

import java.util.Map;

import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.util.Identifiers;

public final class SingleStateExpression extends AbstractStateExpression {
  
  private final String name;
  private ArrayExpression mem, size, mark;
  private final Map<String, Object> properties = Maps.newHashMap();
  private final Map<String, BooleanExpression> preAsserts = Maps.newHashMap();
  private final Map<String, BooleanExpression> postAsserts = Maps.newHashMap();
  private BooleanExpression guard;
	private BooleanExpression constraint;
  
  private SingleStateExpression(String _name, 
  		ArrayExpression _mem, ArrayExpression _size, ArrayExpression _mark) {
  	name = _name;
  	mem = _mem;
  	size = _size;
  	mark = _mark;
  }
  
  private SingleStateExpression(String _name) {
  	name = _name;
  }
  
  static SingleStateExpression create(String name, ArrayExpression mem, ArrayExpression size, ArrayExpression mark) {
  	return new SingleStateExpression(name, mem, size, mark);
  }
  
	@Override
	public boolean isSingle() {
		return true;
	}
	
	@Override
	public boolean isMultiple() {
		return false;
	}

	@Override
	public boolean isLambda() {
		return false;
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
		Preconditions.checkArgument(state.isSingle());
		Expression thatMem = state.asSingle().getMemory();
		Expression thatSize = state.asSingle().getSize();
		Expression thatMark = state.asSingle().getMark();
		return mem.getType().equals(thatMem.getType()) &&
				size.getType().equals(thatSize.getType()) &&
				mark.getType().equals(thatMark.getType());
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
		sb.append(mem).append("\n").append(size).append("\n").append(mark).append("\n");
		return sb.toString();
	}

	@Override
	public BooleanExpression getGuard() {
		return guard;
	}

	@Override
	public Map<String, Object> getProperties() {
		return properties;
	}
	
	@Override
	public void setProperties(Map<String, Object> props) {
	  properties.putAll(props);
	}

	@Override
	public Object setProperty(String key, Object val) {
		return properties.put(key, val);
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
	public boolean hasProperty(String label) {
	  return properties.containsKey(label);
	}
	
	@Override
	public ArrayType[] getElemTypes() {
		return new ArrayType[]{mem.getType(), size.getType(), mark.getType()};
	}

	@Override
	public Map<String, BooleanExpression> getPreAssertions() {
		return preAsserts;
	}

	@Override
	public Map<String, BooleanExpression> getPostAssertions() {
		return postAsserts;
	}

	String getName() {
		return name;
	}

	ArrayExpression getMemory() {
		return mem;
	}
	
  void setMemory(ArrayExpression mem) {
  	this.mem = mem;
	}
	
	ArrayExpression getSize() {
		return size;
	}
	
  void setSize(ArrayExpression size) {
  	this.size = size;
	}
  
  ArrayExpression getMark() {
  	return mark;
  }
  
  void setMark(ArrayExpression mark) {
  	this.mark = mark;
  }
  
	int getElemSize() {
		return 3;
	}
}
