package edu.nyu.cascade.prover;

import edu.nyu.cascade.prover.type.IntegerType;


/**
 * The interface that tags the expression as an integer expression. Methods for
 * all operations on integers are provided. These methods should use the same
 * expression manager that the expression itself is using. 
 *  
 * @author <a href="mailto:dejan@cs.nyu.edu">Dejan Jovanović</a>
 */
public interface IntegerExpression extends Expression {
	
  /**
	 * Returns a new Boolean expression that represents a greater than  
	 * (>) over this expression and a given integer expression <code>e</code>. 
	 * @param e expression to compare to
	 * @return the greater than expression
	 */
	BooleanExpression greaterThan(Expression e) ;
	
	/**
	 * Returns a new Boolean expression that represents a greater than or equal
	 * comparison (>=) over this expression and a given integer expression <code>e</code>. 
	 * @param e expression to compare to
	 * @return the greater than or equal expression
	 */
	BooleanExpression greaterThanOrEqual(Expression e) ;

	/**
	 * Returns a new Boolean expression that represents a less than comparison 
	 * (<) over this expression and a given integer expression <code>e</code>. 
	 * @param e expression to compare to
	 * @return the less than expression
	 */
	BooleanExpression lessThan(Expression e) ;

	/**
	 * Returns a new Boolean expression that represents a less than or equal
	 * comparison (<=) over this expression and a given integer expression <code>e</code>. 
	 * @param e expression to compare to
	 * @return the less than expression
	 */
	BooleanExpression lessThanOrEqual(Expression e) ;
	
	/**
	 * Returns a new Integer expression that is the sum of this expression
	 * and a given expression <code>e</code>.
	 * @param e the expression to add
	 * @return the sum expression
	 */	
	IntegerExpression plus(Expression e) ;
	
	/**
	 * Returns a new Integer expression that is the sum of this expression
	 * and a given expression <code>rest</code>.
	 * @param rest the expression to add
	 * @return the sum expression
	 */	
	IntegerExpression plus(IntegerExpression... rest);
	
	/**
	 * Returns a new Integer expression that is the sum of this expression
	 * and a given expression <code>rest</code>.
	 * @param rest the expression to add
	 * @return the sum expression
	 */	
	IntegerExpression plus(Iterable<? extends IntegerExpression> rest);

	/**
	 * Returns a new Integer expression that is the difference of this expression
	 * and a given expression <code>e</code>.
	 * @param e the expression to subtract
	 * @return the difference expression
	 */
	IntegerExpression minus(Expression e) ;
	
	IntegerExpression negate();
	/**
	 * Returns a new Integer expression that is the multiplication of this expression
	 * and a given expression <code>e</code>.
	 * @param e the expression to multiply with
	 * @return the multiplication expression
	 */
	IntegerExpression times(Expression e) ;
	
	/**
	 * Returns a new Integer expression that is the ratio of this expression
	 * and a given expression <code>e</code>.
	 * @param e the expression to divide with
	 * @return the division expression
	 */
	IntegerExpression divides(Expression e) ;
	
	/**
     * Returns a new Integer expression that is the ratio of this expression
     * and a given expression <code>e</code>.
     * @param e the expression to divide with
     * @return the remainder expression
     */
	IntegerExpression mods(Expression e) ;
	
	/**
	 * Returns a new Integer expression that is the exponentiation of this expression
	 * to the power of a given expression <code>e</code>.
	 * @param e the power
	 * @return the power expression
	 */
	IntegerExpression pow(Expression e) ;
	
	@Override
	IntegerType getType();
}
