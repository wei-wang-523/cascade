package edu.nyu.cascade.c.preprocessor.typeanalysis;

import java.util.Map;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.base.Predicates;
import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import xtc.type.Type;
import xtc.type.VariableT;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;

public class IRVarImpl implements IRVar {
	private String name;
	private final Type type;
	private final Scope scope;
	private final Map<String, Set<IRVarImpl>> allocVarMap;
	private final IRVarImpl rootVar;
	private final Set<IRVarImpl> allocVarSet;
	private boolean isNullLoc = false, isFreed = false, isTouched = false;
	
	protected static Predicate<IRVarImpl> isFreePredicate  = new Predicate<IRVarImpl>() {
		@Override
		public boolean apply(IRVarImpl var) {
			return var.isFreed;
		}
	};
	
	protected static Predicate<IRVarImpl> isNullPredicate  = new Predicate<IRVarImpl>() {
		@Override
		public boolean apply(IRVarImpl var) {
			return var.isNullLoc;
		}
	};
	
	protected static Predicate<IRVarImpl> isTouchedPredicate  = new Predicate<IRVarImpl>() {
		@Override
		public boolean apply(IRVarImpl var) {
			return var.isTouched;
		}
	};
	
	private IRVarImpl(String _name, Type _type, Scope _scope, IRVarImpl _rootVar) {
		name = _name;
		type = _type;
		scope = _scope;
		rootVar = _rootVar;
		
		if(_type.resolve().isPointer()) {
			// Non pointer variable without allocated variables
			allocVarMap = null;
			allocVarSet = Sets.newLinkedHashSet();
		} else {
			allocVarSet = null;
			// Only structure or union pointer might with allocate variable map
			if(_type.resolve().isStruct() || _type.resolve().isUnion()) {
				boolean hasPointerMember = Iterables.any(_type.resolve().toStructOrUnion().getMembers(),
						new Predicate<VariableT>() {
					@Override
					public boolean apply(VariableT elem) {
						return elem.resolve().isPointer();
					}
				});
				if(hasPointerMember) 	
					allocVarMap = Maps.newLinkedHashMap();
				else
					allocVarMap = null;
			} else {
				allocVarMap = null;
			}
		}
	}
	  
	protected static IRVarImpl create(String _name, Type _type, Scope _scope) {
		return createWithRoot(_name, _type, _scope, null);
	}
	
	protected static IRVarImpl createWithRoot(String _name, Type _type, Scope _scope, IRVarImpl _root) {
		return new IRVarImpl(_name, _type, _scope, _root);
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
		return scope.getQualifiedName();
	}
	
	@Override
  public boolean isNullLoc() {
		return isNullLoc;
  }
	
  @Override
  public boolean equals(Object o) {
    if(!(o instanceof IRVarImpl)) return false;
    IRVarImpl var = (IRVarImpl) o;
    return name.equals(var.getName()) && type == var.getType() && scope.equals(var.getScope());
  }
	
  @Override
	public String toString() {
	  StringBuilder sb = new StringBuilder().append(name);
	  if(isFreed) sb.append(".free");
	  if(isNullLoc)	sb.append(".null");
	  if(scope != null) sb.append(scope.getQualifiedName());
	  if(type != null)	sb.append("(type ").append(type.getName()).append(") ");
	  return sb.toString();
	}

	/**
   * Check if <code>allocVarSet</code> contains any earlier created place holder
   * region variable which is nullLoc and untouched. If so, just set <code>isNullLoc 
   * = false</code>, and return it. 
   * 
   * Otherwise, create a new region variable and add it to <code>allocVarSet</code>.
   * 
   * @return a region variable
   */
  protected IRVarImpl createAllocatedVar(Scope scope) {
  	Preconditions.checkArgument(allocVarSet != null);
		IRVarImpl nullVar = Iterables.find(
				getAllocVarSetOutScope(scope), 
				Predicates.and(isNullPredicate, Predicates.not(isTouchedPredicate)), 
				null);
    	
		if(nullVar != null) {
			nullVar.isNullLoc = false; nullVar.touched();
			return nullVar;
  	}
    
  	IRVarImpl regionVar = allocVar(scope);
  	addAllocVarSet(regionVar);
  	return regionVar;
	}

  /**
   * Check if the variable set associate with <code>fieldName</code> in 
   * <code>allocVarMap</code>, contains any earlier created place holder
   * region variable (<code>isNullLoc = true</code>), which is untouched. 
   * If so, just set <code>isNullLoc = false</code>, and return it. 
   * 
   * Otherwise, create a new region variable and add it to the variable set.
   * 
   * @return a region variable
   */
	protected IRVarImpl createAllocatedVarOfField(String fieldName, Scope scope) {
		Preconditions.checkArgument(allocVarMap != null && allocVarMap.containsKey(fieldName));
		
		IRVarImpl nullVar = Iterables.find(
				getAllocVarSetOutScopeOfField(fieldName, scope), 
				Predicates.and(isNullPredicate, Predicates.not(isTouchedPredicate)), 
				null);
  	
  	if(nullVar != null) {
  		nullVar.isNullLoc = false; nullVar.touched();
  		return nullVar;
  	} else {
  		IRVarImpl regionVar = allocVarOfField(fieldName, scope);
  		addAllocVarMap(fieldName, regionVar);
  		return regionVar;
  	}
	}
	
	/**
   * Create a new region variable and add it to <code>allocVarSet</code>.
   * @return a region variable
   */
  protected IRVarImpl createAllocVar(Scope scope) {
  	Preconditions.checkArgument(allocVarSet != null);
  	IRVarImpl regionVar = allocVar(scope);
  	addAllocVarSet(regionVar);
  	return regionVar;
	}

  /**
   * Create a new region variable and add it to the variable set.
   * @return a region variable
   */
	protected IRVarImpl createAllocVarOfField(String fieldName, Scope scope) {
		Preconditions.checkArgument(allocVarMap != null && allocVarMap.containsKey(fieldName));
		IRVarImpl regionVar = allocVarOfField(fieldName, scope);
		addAllocVarMap(fieldName, regionVar);
		return regionVar;
	}

	/**
	 * Create a place holder of allocated region variable for later replacement 
	 * of <code>allocated(...)</code> predicate
	 * @return region variable (is null location)
	 */
	protected IRVarImpl createNullAllocVar(Scope scope) {
		IRVarImpl var = allocVar(scope);
		var.isNullLoc = true;
		addAllocVarSet(var);
		return var;
	}

	/**
	 * Create a place holder of allocated region variable for later replacement 
	 * of <code>allocated(...)</code> predicate
	 * @param fieldName
	 * @return region variable (is null location)
	 */
	protected IRVarImpl createNullAllocVarOfField(String fieldName, Scope scope) {
		IRVarImpl var = allocVarOfField(fieldName, scope);
		var.isNullLoc = true;
		addAllocVarMap(fieldName, var);
		return var;
	}

	/**
	 * Free all the region variables defined in <code>scope</code> or its nested scopes
	 * @param scope
	 */
	protected void freeAllocVar(final Scope scope) {
		Iterable<IRVarImpl> resSet = Iterables.filter(allocVarSet, new Predicate<IRVarImpl>(){
					@Override
					public boolean apply(IRVarImpl var) {
						return scope.hasNested(var.getScope().getName()) || scope.equals(var.getScope());
					}
		});
		for(IRVarImpl res: resSet)	res.free();
	}

	/**
	 * Free all the region variables associated with <code>fieldName</code>
	 * defined in <code>scope</code> or its nested scopes
	 * @param fieldName
	 * @param scope
	 */
	protected void freeAllocVarOfField(String fieldName, final Scope scope) {
		Iterable<IRVarImpl> resSet = 
				Iterables.filter(allocVarMap.get(fieldName), new Predicate<IRVarImpl>(){
					@Override
					public boolean apply(IRVarImpl var) {
						return scope.hasNested(var.getScope().getName()) || scope.equals(var.getScope());
					}
				});
		for(IRVarImpl res: resSet)	res.free();
	}

	/**
	 * Get the <code>rootVar</code>
	 */
	protected IRVarImpl getRootVar() {
		return rootVar;
	}
	
	/**
	 * Get the set of allocated region variables defined in
	 * <code>scope</code> or or out of <code>scope</code>.
	 * 
	 * @param scope
	 */
	protected Iterable<IRVarImpl> getAllocVarSetOutScope(final Scope scope) {
		Preconditions.checkArgument(allocVarSet != null);
		// Only returns the region variables defined in the same or parent scope
		return Iterables.filter(allocVarSet, new Predicate<IRVarImpl>() {
			@Override
			public boolean apply(IRVarImpl var) {
				return var.getScope().equals(scope) || var.getScope().hasNested(scope.getName());
			}
		});
	}
	
	/**
	 * Get the set of allocated variables associate with <code>fieldName</code> 
	 * in <code>allocVarMap</code>, which is defined in <code>scope</code>, 
	 * or out of <code>scope</code>. 
	 * 
	 * @param fieldName
	 * @param scope 
	 * @return  a set of region variables
	 */
	protected Iterable<IRVarImpl> getAllocVarSetOutScopeOfField(String fieldName, final Scope scope) {
		Preconditions.checkArgument(allocVarMap != null);
		Preconditions.checkArgument(allocVarMap.containsKey(fieldName));
		Type fieldType = type.resolve().toStructOrUnion().lookup(fieldName);
		if(!fieldType.resolve().isPointer()) {
			return Sets.newHashSet(this);
		} else {
			// Only returns the region variables defined in the same or parent scope
			return Iterables.filter(allocVarMap.get(fieldName), new Predicate<IRVarImpl>() {
				@Override
				public boolean apply(IRVarImpl var) {
					return var.getScope().equals(scope) || var.getScope().hasNested(scope.getName());
				}
			});
		}
	}
	
	protected String toStringShort() {
	  StringBuilder sb = new StringBuilder();
	  sb.append(name);
	  if(isFreed) sb.append(".free");
	  if(isNullLoc)	sb.append(".null");
	  return sb.toString();
	}

	/**
	 * Add <code>var</code> to <code>allocVarSet</code>
	 * @param var
	 * @return <code>true</code> if <code>allocVarSet</code> 
	 * did not already contain the specified element
	 */
	private boolean addAllocVarSet(IRVarImpl var) {
		Preconditions.checkArgument(allocVarSet != null);
		return allocVarSet.add(var);
	}

	/**
	 * Push pair (<code>fieldName</code>, <code>var</code>) into
	 * <code>allocVarMap</code>.
	 * @param fieldName
	 * @param var
	 * @return the previous value associated with key, or null if there was no 
	 * mapping for key. 
	 */
	private IRVarImpl addAllocVarMap(String fieldName, IRVarImpl var) {
		Preconditions.checkArgument(allocVarMap != null);
		if(allocVarMap.containsKey(fieldName)) {
			Set<IRVarImpl> set = allocVarMap.get(fieldName);
			set.add(var);
			allocVarMap.put(fieldName, set);
		} else {
			Set<IRVarImpl> set = Sets.newHashSet(var);
			allocVarMap.put(fieldName, set);
		}
		return var;
	}

	/**
	 * Allocate a region variable for this variable
	 * @return a region variable
	 */
	private IRVarImpl allocVar(Scope scope) {
		Preconditions.checkArgument(type.resolve().isPointer());
		Type varType = type.resolve().toPointer().getType().resolve();
		String	varName = Identifiers.uniquify(
				new StringBuilder().append(Identifiers.REGION_VARIABLE_NAME).append(name).toString());
		IRVarImpl regionVar = createWithRoot(varName, varType, scope, this);
		return regionVar;
	}

	/**
	 * Allocate a region variable with the <code>fieldName</code>
	 * @param fieldName
	 * @return a region variable
	 */
	private IRVarImpl allocVarOfField(String fieldName, Scope scope) {
		Preconditions.checkArgument(type.resolve().isStruct() || type.resolve().isUnion());
		Type fieldType = type.resolve().toStructOrUnion().lookup(fieldName).resolve();
		assert fieldType.isPointer();
		Type varType = fieldType.toPointer().getType();
		String varName = Identifiers.uniquify(
				new StringBuilder()
				.append(name).append(Identifiers.RECORD_SELECT_NAME_INFIX).append(fieldName).toString());		
		IRVarImpl regionVar = createWithRoot(varName, varType, scope, this);
		return regionVar;
	}
	
	private Scope getScope() {
		return this.scope;
	}

	private boolean free() {
		if(this.isFreed) {
			IOUtils.err().println("WARNING: double free " + toStringShort());
			return false;
		} else {
			this.isFreed = true;
			return true;
		}
	}
	
	private void touched() {
		Preconditions.checkArgument(!isTouched);
		this.isTouched = true;
	}
}
