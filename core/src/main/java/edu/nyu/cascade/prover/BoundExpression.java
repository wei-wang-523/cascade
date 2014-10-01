package edu.nyu.cascade.prover;


/**
 * Interface for the expressions that represent expressions.
 * @author <a href="mailto:dejan@cs.nyu.edu">Dejan Jovanović</a>
 */
public interface BoundExpression extends Expression {

	/** 
	 * Returns the name of the bound expression.
	 * @return the name
	 */
	public String getName();
}
