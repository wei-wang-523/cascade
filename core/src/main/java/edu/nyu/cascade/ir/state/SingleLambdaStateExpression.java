package edu.nyu.cascade.ir.state;

import java.util.Arrays;
import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;

import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Table;

import edu.nyu.cascade.ir.memory.safety.PredicateClosure;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public final class SingleLambdaStateExpression extends AbstractStateExpression {
  
	enum LabelType {
		HEAP,
		STACK,
		OTHER
	}
	
	/** Map uninterpreted safety predicate function expression to arguments 
	 * (all labels, not real expressions), waiting to be substituted with
	 * initial boolean value (true or false)
	 */
  private Multimap<Expression, Collection<Expression>> predicateMap = HashMultimap.create();
  
  /** Map fresh label(place-holder) to real expression */
  private final Table<VariableExpression, LabelType, Expression> labelTable = HashBasedTable.create();

  /** Store all safety predicate closures */
  private final Map<String, PredicateClosure> safetyPredicateClosures = Maps.newHashMap();
  
  /** Store all safety predicates */
  private final Map<String, BooleanExpression> safetyPredicates = Maps.newHashMap();
  
  private final SingleStateExpression singleState;
  private BooleanExpression constraint;
  private BooleanExpression guard;
  
  private SingleLambdaStateExpression(SingleStateExpression singleState) {
  	Preconditions.checkNotNull(singleState);
  	this.singleState = singleState;
  }
  
  static SingleLambdaStateExpression create(SingleStateExpression singleState) {
  	return new SingleLambdaStateExpression(singleState);
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
		return true;
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
  	return singleState.hasScope();
  }

	@Override
	public void setScope(Scope _scope) {
		singleState.setScope(_scope);
	}

	@Override
	public Scope getScope() {
		return singleState.getScope();
	}
	
	@Override
	public boolean hasSameType(StateExpression state) {
		return singleState.hasSameType(state.asSingleLambda().getSingleState());
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append(toStringShort());
		if(constraint != null) 
			sb.append("constraint: ").append(constraint).append('\n');
		if(guard != null) 
			sb.append("guard: ").append(guard);
		if(!safetyPredicateClosures.isEmpty()) {
			for(Entry<String, PredicateClosure> entry : safetyPredicateClosures.entrySet())
				sb.append('\n').append(entry.getKey()).append(": ").append(entry.getValue());
		}
		if(!safetyPredicates.isEmpty()) {
			for(Entry<String, BooleanExpression> entry : safetyPredicates.entrySet())
				sb.append('\n').append(entry.getKey()).append(": ").append(entry.getValue());
		}
		return sb.toString();
	}
	
	@Override
	public String toStringShort() {
		return singleState.toStringShort();
	}

	@Override
	public BooleanExpression getGuard() {
		return guard;
	}

	@Override
	public Map<String, Object> getProperties() {
		return singleState.getProperties();
	}

	@Override
	public void setProperties(Map<String, Object> props) {
		singleState.setProperties(props);
	}

	@Override
	public Object setProperty(String key, Object val) {
		return singleState.setProperty(key, val);
	}

	@Override
	public Object getProperty(String label) {
	  return singleState.getProperty(label);
	}
	
	@Override
	public void setPreAssertion(String label, BooleanExpression assertion) {
		singleState.setPreAssertion(label, assertion);
	}
	
	@Override
	public void setPostAssertion(String label, BooleanExpression assertion) {
		singleState.setPostAssertion(label, assertion);
	}

	@Override
	public boolean hasProperty(String label) {
	  return singleState.hasProperty(label);
	}
	
	@Override
	public Type[] getElemTypes() {
		return singleState.getElemTypes();
	}
	
	@Override
	public Map<String, BooleanExpression> getPreAssertions() {
		return singleState.getPreAssertions();
	}

	@Override
	public Map<String, BooleanExpression> getPostAssertions() {
		return singleState.getPostAssertions();
	}
	
	public Multimap<Expression, Collection<Expression>> getPredicateMap() {
		return predicateMap;
	}

	public void putSafetyPredicateClosure(String label, PredicateClosure predicateClosure) {
		safetyPredicateClosures.put(label, predicateClosure);
	}

	public void putSafetyPredicate(String label, BooleanExpression predicate) {
		safetyPredicates.put(label, predicate);
	}

	public PredicateClosure getSafetyPredicateClosure(String label) {
		Preconditions.checkArgument(safetyPredicateClosures.containsKey(label));
		return safetyPredicateClosures.get(label);
	}

	public BooleanExpression getSafetyPredicate(String label) {
		Preconditions.checkArgument(safetyPredicates.containsKey(label));
		return safetyPredicates.get(label);
	}

	public void registerPredicate(Expression predicate, Expression... args) {
	  predicateMap.put(predicate, Arrays.asList(args));
	}

	public String getName() {
		return singleState.getName();
	}

	public void setPredicateMap(
	    Multimap<Expression, Collection<Expression>> _predicateMap) {
		Preconditions.checkNotNull(_predicateMap);
	  predicateMap = _predicateMap;
	}

	int getElemSize() {
		return singleState.getElemSize();
	}

	Map<String, PredicateClosure> getSafetyPredicateClosures() {
		return safetyPredicateClosures;
	}

	Map<String, BooleanExpression> getSafetyPredicates() {
		return safetyPredicates;
	}
	
	Table<VariableExpression, LabelType, Expression> getLabelTable() {
	  return labelTable;
	}
	
	void putLabelTable(Table<VariableExpression, LabelType, Expression> _labelTable) {
	  labelTable.putAll(_labelTable);
	}

	void putAllSafetyPredicateClosures(Map<String, PredicateClosure> map) {
		safetyPredicateClosures.putAll(map);
	}

	void putAllSafetyPredicates(Map<String, BooleanExpression> map) {
		safetyPredicates.putAll(map);
	}

	void putAllPredicateMap(Multimap<Expression, Collection<Expression>> _predicateMap) {
	  predicateMap.putAll(_predicateMap);
  }
  
  void registerLabel(VariableExpression label, Expression arg) {
	  labelTable.put(label, LabelType.OTHER, arg);
  }
  
  void registerHeapLabel(VariableExpression label, Expression arg) {
	  labelTable.put(label, LabelType.HEAP, arg);
  }
  
  void registerStackLabel(VariableExpression label, Expression arg) {
	  labelTable.put(label, LabelType.STACK, arg);
  }

	SingleStateExpression getSingleState() {
	  return singleState;
  }
}
