package edu.nyu.cascade.ir.state;

import java.util.Arrays;
import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import edu.nyu.cascade.ir.memory.safety.PredicateClosure;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;

public final class SingleLambdaStateExpression extends AbstractStateExpression {

	/**
	 * Map uninterpreted safety predicate function expression to arguments (all
	 * labels, not real expressions), waiting to be substituted with initial
	 * boolean value (true or false)
	 */
	private Multimap<Expression, Collection<Expression>> predicateMap = HashMultimap
	    .create();

	/** Store all safety predicate closures */
	private final Map<String, PredicateClosure> safetyPredicateClosures = Maps
	    .newHashMap();

	/** Store all safety predicates */
	private final Map<String, BooleanExpression> safetyPredicates = Maps
	    .newHashMap();

	private final SingleStateExpression singleState;

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
	public String toStringShort() {
		StringBuilder sb = new StringBuilder().append(singleState.toStringShort());
		if (!safetyPredicateClosures.isEmpty()) {
			for (Entry<String, PredicateClosure> entry : safetyPredicateClosures
			    .entrySet())
				sb.append('\n').append(entry.getKey()).append(": ").append(entry
				    .getValue());
		}
		if (!safetyPredicates.isEmpty()) {
			for (Entry<String, BooleanExpression> entry : safetyPredicates.entrySet())
				sb.append('\n').append(entry.getKey()).append(": ").append(entry
				    .getValue());
		}
		return sb.toString();
	}

	public Multimap<Expression, Collection<Expression>> getPredicateMap() {
		return predicateMap;
	}

	public void putSafetyPredicateClosure(String label,
	    PredicateClosure predicateClosure) {
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

	void putAllSafetyPredicateClosures(Map<String, PredicateClosure> map) {
		safetyPredicateClosures.putAll(map);
	}

	void putAllSafetyPredicates(Map<String, BooleanExpression> map) {
		safetyPredicates.putAll(map);
	}

	void putAllPredicateMap(
	    Multimap<Expression, Collection<Expression>> _predicateMap) {
		predicateMap.putAll(_predicateMap);
	}

	SingleStateExpression getSingleState() {
		return singleState;
	}
}
