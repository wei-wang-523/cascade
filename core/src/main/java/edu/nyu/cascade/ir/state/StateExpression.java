package edu.nyu.cascade.ir.state;

import java.util.Collection;
import java.util.Map;

import com.google.common.collect.Multimap;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.VariableExpression;

/**
 * Program state tuple <memory, size, constraint, guard>
 * @author wei
 *
 */

public interface StateExpression {
	
	SingleStateExpression asSingle();
	
	MultiStateExpression asMultiple();
	
	SingleLambdaStateExpression asSingleLambda();
	
	MultiLambdaStateExpression asMultiLambda();

	boolean isSingle();
	
	boolean isMultiple();
	
	boolean isLambda();
  
  BooleanExpression getConstraint();
  
  void setConstraint(BooleanExpression constraint);

	Object setProperty(String key, Object val);
	
	void addConstraint(BooleanExpression constraint);
	
	void addGuard(BooleanExpression guard);
	
	/**
	 * Used for path-based encoding, add guard of pre-state to current state
	 * @param preGuard
	 */
	void addPreGuard(BooleanExpression preGuard);

	BooleanExpression getGuard();
	
	void setGuard(BooleanExpression guard);

	boolean hasProperty(String label);

	Object getProperty(String label);
	
	void addAssertion(String label, BooleanExpression assertion);
	
	Multimap<String, BooleanExpression> getAssertions();
	
	void setProperties(Map<String, Object> props);

	Map<String, Object> getProperties();

	String toStringShort();

	void addVar(VariableExpression variable);
	void addVars(Collection<VariableExpression> variables);
	Collection<VariableExpression> getVars();
	
	void addRegion(VariableExpression region);
	void addRegions(Collection<VariableExpression> regions);
	Collection<VariableExpression> getRegions();
	
	void setAssertions(Multimap<String, BooleanExpression> assertions);

	void setMemTracker(Expression expr);
	
	Expression getMemTracker();

	Map<Expression, Expression> getHoareValues();
	
	void setHoareValues(Map<Expression, Expression> hoareValues);
	
	void updateHoareValue(Expression key, Expression Value);
}
