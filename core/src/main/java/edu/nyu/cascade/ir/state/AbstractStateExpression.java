package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.util.Preferences;

public abstract class AbstractStateExpression implements StateExpression {
	private final Multimap<String, BooleanExpression> asserts = HashMultimap
			.create();
	private final Map<String, Object> properties = Maps.newHashMap();
	private BooleanExpression guard;
	private BooleanExpression constraint;

	/**
	 * Keep track the memory leak issue with option memory-check enabled
	 */
	private Expression memTracker;

	/**
	 * Keep record of local variables and newly allocated regions with option
	 * -sbe(small block based encoding) enabled
	 */
	private final Collection<VariableExpression> vars = Lists.newArrayList();
	private final Collection<VariableExpression> regions = Lists.newArrayList();

	private final Map<Expression, Expression> hoareValues = Maps.newHashMap();

	@Override
	public SingleStateExpression asSingle() {
		Preconditions.checkArgument(!isLambda());
		Preconditions.checkArgument(isSingle());
		return (SingleStateExpression) this;
	}

	@Override
	public SingleLambdaStateExpression asSingleLambda() {
		Preconditions.checkArgument(isLambda());
		Preconditions.checkArgument(isSingle());
		return (SingleLambdaStateExpression) this;
	}

	@Override
	public MultiStateExpression asMultiple() {
		Preconditions.checkArgument(!isLambda());
		Preconditions.checkArgument(isMultiple());
		return (MultiStateExpression) this;
	}

	@Override
	public MultiLambdaStateExpression asMultiLambda() {
		Preconditions.checkArgument(isLambda());
		Preconditions.checkArgument(isMultiple());
		return (MultiLambdaStateExpression) this;
	}

	@Override
	final public void addPreGuard(BooleanExpression preGuard) {
		BooleanExpression guard = getGuard();
		ExpressionManager exprManager = guard.getExpressionManager();
		BooleanExpression tt = exprManager.tt();
		if (preGuard.equals(tt))
			return;
		guard = preGuard.ifThenElse(guard, exprManager.ff()).asBooleanExpression();
		setGuard(guard);
	}

	@Override
	final public void addGuard(BooleanExpression _guard) {
		BooleanExpression guard = getGuard();
		ExpressionManager exprManager = guard.getExpressionManager();
		BooleanExpression tt = exprManager.tt();
		if (!guard.equals(tt)) {
			guard = guard.ifThenElse(_guard, exprManager.ff()).asBooleanExpression();
		} else {
			guard = _guard;
		}
		setGuard(guard);
	}

	@Override
	final public void addConstraint(BooleanExpression _constraint) {
		if (_constraint == null)
			return;
		BooleanExpression constraint = getConstraint();
		if (constraint != null) {
			constraint = constraint.and(_constraint);
		} else {
			constraint = _constraint;
		}
		setConstraint(constraint);
	}

	@Override
	final public void addAssertion(String label, BooleanExpression assertion) {
		asserts.put(label, assertion);
	}

	@Override
	final public Multimap<String, BooleanExpression> getAssertions() {
		return asserts;
	}

	@Override
	final public void setAssertions(
			Multimap<String, BooleanExpression> assertions) {
		asserts.putAll(assertions);
	}

	@Override
	final public void addVar(VariableExpression variable) {
		if (!Preferences.isSet(Preferences.OPTION_SBE))
			return;
		vars.add(variable);
	}

	@Override
	final public void addRegion(VariableExpression region) {
		if (!Preferences.isSet(Preferences.OPTION_SBE))
			return;
		regions.add(region);
	}

	@Override
	final public void addVars(Collection<VariableExpression> variables) {
		vars.addAll(variables);
	}

	@Override
	final public void addRegions(Collection<VariableExpression> _regions) {
		regions.addAll(_regions);
	}

	@Override
	final public Collection<VariableExpression> getVars() {
		return vars;
	}

	@Override
	final public Collection<VariableExpression> getRegions() {
		return regions;
	}

	@Override
	final public void setMemTracker(Expression expr) {
		memTracker = expr;
	}

	@Override
	final public Expression getMemTracker() {
		return memTracker;
	}

	@Override
	final public Map<Expression, Expression> getHoareValues() {
		return hoareValues;
	}

	@Override
	final public void setHoareValues(Map<Expression, Expression> _hoareValues) {
		hoareValues.putAll(_hoareValues);
		;
	}

	@Override
	final public void updateHoareValue(Expression key, Expression value) {
		hoareValues.put(key, value);
	}

	@Override
	final public String toString() {
		StringBuilder sb = new StringBuilder().append(toStringShort());
		if (constraint != null)
			sb.append("constraint: ").append(constraint).append("\n");
		if (guard != null)
			sb.append("guard: ").append(guard);
		return sb.toString();
	}

	@Override
	final public boolean hasProperty(String label) {
		return properties.containsKey(label);
	}

	@Override
	final public Object getProperty(String label) {
		Preconditions.checkArgument(hasProperty(label));
		return properties.get(label);
	}

	@Override
	final public void setProperties(Map<String, Object> props) {
		properties.putAll(props);
	}

	@Override
	final public Map<String, Object> getProperties() {
		return properties;
	}

	@Override
	final public void setConstraint(BooleanExpression constraint) {
		this.constraint = constraint;
	}

	@Override
	final public void setGuard(BooleanExpression guard) {
		this.guard = guard;
	}

	@Override
	final public BooleanExpression getConstraint() {
		return constraint;
	}

	@Override
	final public Object setProperty(String key, Object val) {
		return properties.put(key, val);
	}

	@Override
	final public BooleanExpression getGuard() {
		return guard;
	}
}
