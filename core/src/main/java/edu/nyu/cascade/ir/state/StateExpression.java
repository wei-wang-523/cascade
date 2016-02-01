package edu.nyu.cascade.ir.state;

import java.util.Map;

import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.type.Type;

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
  
  void setScope(Scope scope);
  
  Scope getScope();
  
  boolean hasScope();
  
  BooleanExpression getConstraint();
  
  void setConstraint(BooleanExpression constraint);
  
  boolean hasSameType(StateExpression state);

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
	
	void setPreAssertion(String label, BooleanExpression assertion);
	
	void setPostAssertion(String label, BooleanExpression assertion);
	
	Map<String, BooleanExpression> getPreAssertions();

	Map<String, BooleanExpression> getPostAssertions();
	
	void setProperties(Map<String, Object> props);

	Map<String, Object> getProperties();

	String toStringShort();

	Type[] getElemTypes();
}
