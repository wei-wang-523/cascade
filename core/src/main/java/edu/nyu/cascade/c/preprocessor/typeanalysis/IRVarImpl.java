package edu.nyu.cascade.c.preprocessor.typeanalysis;

import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import xtc.type.Type;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.util.Identifiers;

public class IRVarImpl implements IRVar {
	private String name;
	private final Type type;
	private final String scope;
	private final Map<String, IRVarImpl> allocVarMap;
	private final IRVarImpl rootVar;
	private IRVarImpl allocVar = null;
	
	private IRVarImpl(String _name, Type _type, String _scope, IRVarImpl _rootVar) {
		name = _name;
		type = _type;
		scope = _scope;
		rootVar = _rootVar;
		allocVarMap = Maps.newLinkedHashMap();
	}
	  
	protected static IRVarImpl create(String _name, Type _type, String _scope) {
		return new IRVarImpl(_name, _type, _scope, null);
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
	public String getScope() {
		return scope;
	}

	@Override
  public boolean isNullLoc() {
		return name.equals(Identifiers.NULL_LOC_NAME);
  }
	
  @Override
  public boolean equals(Object o) {
    if(!(o instanceof IRVarImpl)) return false;
    IRVarImpl var = (IRVarImpl) o;
    return name.equals(var.getName()) && type == var.getType() && scope.equals(var.getScope());
  }
	
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append(name);
    if(scope != null) 
      sb.append(scope);
    if(type != null)
      sb.append("(type ").append(type.getName()).append(") ");
    return sb.toString();
  }
  
  protected IRVarImpl allocVar() {
  	Preconditions.checkArgument(type.resolve().isPointer());
		Type varType = type.resolve().toPointer().getType().resolve();
		String	varName = Identifiers.uniquify(
				new StringBuilder().append(Identifiers.REGION_VARIABLE_NAME).append(name).toString());
		String varScope = this.scope;
		IRVarImpl regionVar = new IRVarImpl(varName, varType, varScope, this);
		
		allocVar = regionVar;
		return regionVar;
	}
  
  protected IRVarImpl allocVarOfField(String fieldName) {
		Preconditions.checkArgument(type.resolve().isStruct() || type.resolve().isUnion());
		Type fieldType = type.resolve().toStructOrUnion().lookup(fieldName).resolve();
		assert fieldType.isPointer();
		Type varType = fieldType.toPointer().getType();
		String varName = Identifiers.uniquify(
				new StringBuilder()
				.append(name).append(Identifiers.RECORD_SELECT_NAME_INFIX).append(fieldName).toString());		
		String varScope = this.scope;
		IRVarImpl regionVar = new IRVarImpl(varName, varType, varScope, this);
		
		allocVarMap.put(fieldName, regionVar);
		return regionVar;
	}

  protected IRVarImpl createAllocVar() {
  	IRVarImpl regionVar = allocVar();
  	allocVar = regionVar;
  	return regionVar;
	}

	protected IRVarImpl createAllocVarOfField(String fieldName) {		
		IRVarImpl regionVar = allocVarOfField(fieldName);
		allocVarMap.put(fieldName, regionVar);
		return regionVar;
	}

	protected IRVarImpl getRootVar() {
		return rootVar;
	}

	protected IRVarImpl getAllocVar() {
		return allocVar;
	}

	protected IRVarImpl getAllocVarOfField(String fieldName) {
		assert type.resolve().isStruct() || type.resolve().isUnion();
		Type fieldType = type.resolve().toStructOrUnion().lookup(fieldName);
		if(!fieldType.resolve().isPointer())
			return this;
		else {
			Preconditions.checkArgument(allocVarMap.containsKey(fieldName));
			return allocVarMap.get(fieldName);
		}
	}

	protected String toStringShort() {
    StringBuilder sb = new StringBuilder();
    return sb.append(name).toString();
  }

	/**
	 * Create a place holder for later replacement of allocated(...) predicate
	 * @return
	 */
	private IRVarImpl allocNull() {
		Preconditions.checkArgument(type.resolve().isPointer());
		Type varType = type.resolve().toPointer().getType().resolve();
		String	varName = Identifiers.NULL_LOC_NAME;
		String varScope = this.scope;
		IRVarImpl regionVar = new IRVarImpl(varName, varType, varScope, this);
		
		allocVar = regionVar;
		return regionVar;
	}

  /**
	 * Create a place holder for later replacement of allocated(...) predicate
   * @param fieldName
   * @return
   */
	private IRVarImpl allocNullOfField(String fieldName) {
		Preconditions.checkArgument(type.resolve().isStruct() || type.resolve().isUnion());
		Type fieldType = type.resolve().toStructOrUnion().lookup(fieldName).resolve();
		assert fieldType.isPointer();
		Type varType = fieldType.toPointer().getType();
		String varName = Identifiers.NULL_LOC_NAME;	
		String varScope = this.scope;
		IRVarImpl regionVar = new IRVarImpl(varName, varType, varScope, this);
		
		allocVarMap.put(fieldName, regionVar);
		return regionVar;
	}
}
