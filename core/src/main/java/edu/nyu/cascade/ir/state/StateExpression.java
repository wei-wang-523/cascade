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
	
	boolean hasConstraint();
	
	boolean hasGuard();
	
	void addConstraint(BooleanExpression constraint, BooleanExpression tt, BooleanExpression ff);
	
	void addGuard(BooleanExpression guard);

	BooleanExpression getGuard();
	
	void setGuard(BooleanExpression guard);

	boolean hasProperty(String label);

	Object getProperty(String label);

	void setProperties(Map<String, Object> props);

	Map<String, Object> getProperties();

	String toStringShort();

	Type[] getElemTypes();
	
  /**
   * Create a clone of itself to keep clean of side-effect caused by 
   * following operations. Used in the <code>SimplePathEncoding</code> to 
   * analyze statements. Otherwise, the side-effect caused of the expression 
   * evaluation will change the
   * input state, which might also be the input state of other statements
   *  (e.g. in ite-branch), the side-effect of the if-branch 
   * statements will affect the analysis of else-branch statements
   * @param state
   * @return
   */
	StateExpression copy();
}
