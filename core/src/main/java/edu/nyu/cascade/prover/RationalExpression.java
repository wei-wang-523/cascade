package edu.nyu.cascade.prover;

/**
 * The interface that tags the expression as a rational expression. Methods for
 * all needed operations on rational numbers are provided. These methods should
 * use the same expression manager that the expression itself is using.
 * 
 * @author <a href="mailto:dejan@cs.nyu.edu">Dejan Jovanović</a>
 */
public interface RationalExpression extends Expression {

	/**
	 * Returns a new Boolean expression that represents a greater than comparison
	 * (>) over this expression and a given rational expression <code>e</code>.
	 * 
	 * @param e
	 *          expression to compare to
	 * @return the greater than or equal expression
	 */
	public BooleanExpression gt(Expression e);

	/**
	 * Returns a new Boolean expression that represents a greater than or equal
	 * comparison (>=) over this expression and a given rational expression
	 * <code>e</code>.
	 * 
	 * @param e
	 *          expression to compare to
	 * @return the greater than or equal expression
	 */
	public BooleanExpression geq(Expression e);

	/**
	 * Returns a new Boolean expression that represents a less than comparison (<)
	 * over this expression and a given rational expression <code>e</code>.
	 * 
	 * @param e
	 *          expression to compare to
	 * @return the less than expression
	 */
	public BooleanExpression lt(Expression e);

	/**
	 * Returns a new Boolean expression that represents a less than or equal
	 * comparison (<=) over this expression and a given rational expression
	 * <code>e</code>.
	 * 
	 * @param e
	 *          expression to compare to
	 * @return the less than expression
	 */
	public BooleanExpression leq(Expression e);

	/**
	 * Returns a new rational expression that is the sum of this expression and a
	 * given expression <code>e</code>.
	 * 
	 * @param e
	 *          the expression to add
	 * @return the sum expression
	 */
	public RationalExpression plus(Expression e);

	/**
	 * Returns a new rational expression that is the difference of this expression
	 * and a given expression <code>e</code>.
	 * 
	 * @param e
	 *          the expression to subtract
	 * @return the difference expression
	 */
	public RationalExpression minus(Expression e);

	/**
	 * Returns a new rational expression that is the multiplication of this
	 * expression and a given expression <code>e</code>.
	 * 
	 * @param e
	 *          the expression to multiply with
	 * @return the multiplication expression
	 */
	public RationalExpression mult(Expression e);

	/**
	 * Returns a new rational expression that is the ratio of this expression and
	 * a given expression <code>e</code>.
	 * 
	 * @param e
	 *          the expression to divide with
	 * @return the division expression
	 */
	public RationalExpression divide(Expression e);

	/**
	 * Returns a new rational expression that is the exponentiation of this
	 * expression to the power of a given expression <code>e</code>.
	 * 
	 * @param e
	 *          the power
	 * @return the power expression
	 */
	public RationalExpression pow(Expression e);
}
