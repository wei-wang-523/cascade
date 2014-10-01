package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Identifiers;

public final class SingleStateExpression extends AbstractStateExpression {
  
  private final String name;
  private final List<Expression> elements;
  private final int size;
  private final Map<String, Object> properties = Maps.newHashMap();
  private BooleanExpression guard;
	private BooleanExpression constraint;
  
  private SingleStateExpression(String _name, 
  		List<Expression> expressions) {
  	Preconditions.checkNotNull(expressions);
  	elements  = expressions;
  	size = elements.size();
  	name = _name;
  }
  
  static SingleStateExpression create(String name, Iterable<? extends Expression> expressions) {
  	return new SingleStateExpression(name, 
  			Lists.newArrayList(expressions));
  }
  
  static SingleStateExpression create(String name, Expression... expressions) {
  	return new SingleStateExpression(name, 
  			Lists.newArrayList(expressions));
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
		Iterator<? extends Expression> thisElemItr = elements.iterator();
		Iterator<? extends Expression> thatElemItr = state.asSingle().getElements().iterator();
		
		while(thisElemItr.hasNext() && thatElemItr.hasNext()) {
			Expression thisElem = thisElemItr.next();
			Expression thatElem = thatElemItr.next();
			if(thisElem.getType().equals(thatElem.getType())) continue;
			return false;
		}
		
		if(thisElemItr.hasNext() || thatElemItr.hasNext()) return false;
		
		return true;
	}
	
	@Override
  public boolean hasConstraint() {
	  return constraint != null;
  }
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for(Expression expr : elements) {
			sb.append(expr).append("\n");
		}
		for(String prop : properties.keySet()) {
			sb.append(prop).append(": ").append(properties.get(prop)).append("\n");
		}
		return sb.toString();
	}
	
	@Override
	public String toStringShort() {
		StringBuilder sb = new StringBuilder();
		for(Expression expr : elements) {
			sb.append(expr.simplify()).append("\n");
		}
		return sb.toString();
	}

	@Override
	public boolean hasGuard() {
	  return guard != null;
	}

	@Override
	public BooleanExpression getGuard() {
		Preconditions.checkArgument(hasGuard());
		return guard;
	}

	@Override
	public void addGuard(BooleanExpression _guard) {
		if(hasGuard()) {
			guard = guard.and(_guard);
		} else {
			setGuard(_guard);
		}
	}

	@Override
	public void addConstraint(BooleanExpression _constraint, BooleanExpression tt, BooleanExpression ff) {		
		if(hasConstraint() && !constraint.equals(tt)) {
			constraint = _constraint.ifThenElse(constraint, ff).asBooleanExpression();
		} else {
			constraint = _constraint;
		}
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
	  return properties.get(label);
	}

	@Override
	public boolean hasProperty(String label) {
	  return properties.containsKey(label);
	}
	
	@Override
	public Type[] getElemTypes() {
		Type[] res = new Type[size];
		for(int i = 0; i < size; i++) {
			res[i] = elements.get(i).getType();
		}
		return res;
	}
	
  @Override
  public SingleStateExpression copy() {
		SingleStateExpression newState = create(name, elements);
		newState.setConstraint(constraint);
		newState.setGuard(guard);
		newState.setProperties(properties);
    return newState;
  }

	String getName() {
		return name;
	}

	Expression getElement(int index) {
		Preconditions.checkPositionIndex(index, size);
	  return Iterables.get(elements, index);
	}

	Collection<? extends Expression> getElements() {
		return elements;
	}
	
	int getElemSize() {
		return size;
	}
}
