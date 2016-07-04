package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import xtc.tree.Node;
import xtc.util.SymbolTable;
import xtc.util.SymbolTable.Scope;

/**
 * A semantic encoder for expressions, using underlying representation Expr and
 * state Mem. Applying the encoder yields an ExpressionClosure object, which can
 * be evaluated to an Expression given a Mem state input.
 * 
 * @param <Expr>
 *          the underlying representation of the expression
 * @param the
 *          representation of program state in the expression
 */

public interface ExpressionEncoder {
	ExpressionEncoding getEncoding();

	StateFactory<?> getStateFactory();

	SymbolTable.Scope getCurrentScope();

	BooleanExpression toBoolean(StateExpression pre, Node node);

	BooleanExpression toBoolean(StateExpression pre, Node node, Scope scope);

	BooleanExpression toBoolean(StateExpression pre, Node node, boolean negated);

	BooleanExpression toBoolean(StateExpression pre, Node node, boolean negated,
	    Scope scope);

	Expression toExpression(StateExpression pre, Node node);

	Expression toExpression(StateExpression pre, Node node, Scope scope);

	Expression toLval(StateExpression pre, Node node);

	Expression toLval(StateExpression pre, Node node, Scope scope);
}
