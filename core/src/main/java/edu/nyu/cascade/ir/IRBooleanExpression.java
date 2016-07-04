package edu.nyu.cascade.ir;

public interface IRBooleanExpression extends IRExpression {
	/**
	 * Indicates whether the expression represents the negated form of the source
	 * node. For example, for the statement "if(X) {...} else {...}",
	 * <code>getSourceNode()</code> on the "if" branch will return the AST node
	 * for X with <code>isNegated() == false</code>; <code>getSourceNode()</code>
	 * on the "else" branch will return the AST node for X with
	 * <code>isNegated() == true</code>.
	 */
	boolean isNegated();

	/**
	 * Returns the negated form of the target expression, with the same source
	 * node.
	 */
	IRBooleanExpression negate();
}
