package edu.nyu.cascade.c.preprocessor.typeanalysis;

import java.util.Map;

import com.google.common.collect.Maps;

import xtc.type.Type;
import edu.nyu.cascade.c.preprocessor.IRVar;

class VarImpl implements IRVar {
  private final String name;
  private final Type type;
  private final String scopeName;
  private final Map<String, Object> properties;
	
	private VarImpl(String name, Type type, String scopeName) {
		this.name = name;
		this.type = type;
		this.scopeName = scopeName;
		this.properties = Maps.newHashMap();
	}
	
	static VarImpl create(String name, Type type, String scopeName) {
		return new VarImpl(name, type, scopeName);
	}
	
	@Override
	public String toString() {
  	StringBuilder sb = new StringBuilder().append(": ").append(name).append('@').append(scopeName);
  	return sb.toString();
	}

	@Override
  public String getName() {
	  return name;
  }

	@Override
  public Type getType() {
	  return type;
  }

	@Override
  public String getScopeName() {
	  return scopeName;
  }
	
	@Override
  public void setProperty(String id, Object o) {
	  properties.put(id, o);
  }

	@Override
  public Object getProperty(String id) {
	  return properties.get(id);
  }
}
