package edu.nyu.cascade.c.preprocessor.typeanalysis;

import java.util.Map;

import com.google.common.collect.Maps;

import xtc.type.Type;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.prover.Expression;

class VarImpl implements IRVar {
  private final String name;
  private final Type type;
  private final String scopeName;
  private final Expression srcExpr;
  private final Map<String, Object> properties;
  
  private boolean heapTag = false;
	
	private VarImpl(String name, Type type, String scopeName, Expression srcExpr) {
		this.name = name;
		this.type = type;
		this.scopeName = scopeName;
		this.srcExpr = srcExpr;
		this.properties = Maps.newHashMap();
	}
	
	protected static VarImpl createForSymbol(String name, Type type, String scopeName, Expression srcExpr) {
		return new VarImpl(name, type, scopeName, srcExpr);
	}
	
	protected static VarImpl createForRegion(String name, Type type, String scopeName, Expression srcExpr) {
		VarImpl regionVar = new VarImpl(name, type, scopeName, srcExpr);
		regionVar.heapTag = true;
		return regionVar;
	}
	
	@Override
	public String toString() {
  	StringBuilder sb = new StringBuilder();
  	sb.append(srcExpr).append(": ").append(name).append('@').append(scopeName);
  	return sb.toString();
	}

	@Override
  public String toStringShort() {
	  return srcExpr.toString();
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
  public Expression getExpr() {
	  return srcExpr;
  }

	@Override
  public boolean hasHeapTag() {
	  return heapTag;
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
