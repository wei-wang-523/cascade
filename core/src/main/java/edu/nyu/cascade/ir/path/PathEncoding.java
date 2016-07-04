package edu.nyu.cascade.ir.path;

import java.util.Collection;
import java.util.List;

import xtc.tree.Node;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.ValidityResult;

public interface PathEncoding {
	ExpressionEncoding getExpressionEncoding();

	ExpressionEncoder getExpressionEncoder();

	StateFactory<?> getStateFactory();

	/**
	 * Returns the <code>IExpressionManager</code> object used in the underlying
	 * expression encoding.
	 */
	ExpressionManager getExpressionManager();

	StateExpression noop(StateExpression pre);

	StateExpression noop(Collection<StateExpression> preStates);

	StateExpression assume(StateExpression pre, Expression bool, boolean isGuard);

	StateExpression assume(StateExpression pre, IRExpression expr,
	    boolean isGuard) throws PathFactoryException;

	StateExpression assign(StateExpression pre, Expression lval, Node lNode,
	    Expression rval, Node rNode);

	StateExpression assign(StateExpression pre, IRExpression lval,
	    IRExpression rval) throws PathFactoryException;

	StateExpression malloc(StateExpression pre, Expression ptr, Node pNode,
	    Expression size);

	StateExpression malloc(StateExpression pre, IRExpression ptr,
	    IRExpression size) throws PathFactoryException;

	StateExpression calloc(StateExpression pre, Expression ptr, Node pNode,
	    Expression nitem, Expression size);

	StateExpression calloc(StateExpression pre, IRExpression ptr,
	    IRExpression nitem, IRExpression size) throws PathFactoryException;

	StateExpression alloca(StateExpression pre, Expression ptr, Node pNode,
	    Expression size);

	StateExpression alloca(StateExpression pre, IRExpression ptr,
	    IRExpression size) throws PathFactoryException;

	StateExpression free(StateExpression pre, Expression ptr, Node pNode);

	StateExpression free(StateExpression pre, IRExpression ptr)
	    throws PathFactoryException;

	StateExpression havoc(StateExpression pre, Expression lval, Node lNode);

	StateExpression havoc(StateExpression pre, IRExpression lval)
	    throws PathFactoryException;

	StateExpression declare(StateExpression pre, IRExpression lval)
	    throws PathFactoryException;

	StateExpression declare(StateExpression pre, Expression lval, Node lNode);

	StateExpression declareArray(StateExpression pre, IRExpression ptr,
	    IRExpression size) throws PathFactoryException;

	StateExpression declareVarArray(StateExpression pre, Expression ptr,
	    Node pNode, Expression size);

	StateExpression ret(StateExpression pre, IRExpression lval)
	    throws PathFactoryException;

	StateExpression init(StateExpression pre, IRExpression lval,
	    IRExpression rval) throws PathFactoryException;

	StateExpression init(StateExpression pre, Expression lval, Node lNode,
	    Expression rval, Node rNode);

	StateExpression call(StateExpression pre, IRExpression func,
	    IRExpression... args) throws PathFactoryException;

	StateExpression call(StateExpression pre, String funcName, Node funcNode,
	    List<Expression> args, List<Node> argNodes);

	StateExpression emptyState();

	ValidityResult<?> checkAssertion(Expression assertion)
	    throws PathFactoryException;

	SatResult<?> checkPath(StateExpression prefix) throws PathFactoryException;

	/** Clean all the side-effect of instance fields */
	void reset();

	/** Get the trace expression annotation for counter-example generation */
	Expression getTraceExpression();

	/**
	 * Get the information about a condition edge is negated or not for
	 * counter-example generation
	 */
	boolean isEdgeNegated();
}