package edu.nyu.cascade.c.pass.alias.steens;

import java.util.Map;

import com.google.common.collect.Maps;

import edu.nyu.cascade.ir.pass.IRVar;
import xtc.type.Type;

class VarImpl implements IRVar {
  private final ECR ecr;
  private final String name;
  private final Type type;
  private final String scopeName;
  private final Map<String, Object> properties;
  
  VarImpl(String name, Type type, String scopeName, ECR ecr) {
    this.name = name;
    this.type = type;
    this.scopeName = scopeName;
    this.ecr = ecr;
    this.properties = Maps.newHashMap();
  }
  
  ECR getECR() {
    return (ECR) ecr.findRoot();
  }
  
  @Override
  public String toString() {
  	StringBuilder sb = new StringBuilder();
  	sb.append(name).append('@').append(scopeName);
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