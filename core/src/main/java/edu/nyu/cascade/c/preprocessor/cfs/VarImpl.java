package edu.nyu.cascade.c.preprocessor.cfs;

import java.util.Map;

import com.google.common.collect.Maps;

import xtc.type.Type;
import edu.nyu.cascade.c.preprocessor.IRVar;

class VarImpl implements IRVar {
  private final Cell cell;
  private final String name;
  private final Type type;
  private final String scopeName;
  private final Map<String, Object> properties;
  
  VarImpl(String name, Type type, String scopeName, Cell cell) {
    this.name = name;
    this.type = type;
    this.scopeName = scopeName;
    this.cell = cell;
    this.properties = Maps.newHashMap();
  }

  Cell getCell() {
    return cell;
  }
  
	@Override
  public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(name).append('@').append(scopeName)
			.append(" (").append(type)
			.append(") : ");
		
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
