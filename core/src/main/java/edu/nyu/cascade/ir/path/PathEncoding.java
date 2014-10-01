package edu.nyu.cascade.ir.path;

import java.io.PrintStream;
import java.util.Collection;

import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.PathFactoryException;
import edu.nyu.cascade.ir.memory.model.MemoryModel;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateExpressionClosure;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.ValidityResult;

public interface PathEncoding    {
  ExpressionEncoding getExpressionEncoding();
  ExpressionEncoder getExpressionEncoder();
  MemoryModel<?> getMemoryModel();
	StateFactory<?> getStateFactory();
  
  /**
   * Returns the <code>IExpressionManager</code> object used in the underlying
   * expression encoding.
   */
  ExpressionManager getExpressionManager();

  StateExpression noop(StateExpression pre);
  StateExpression noop(Collection<StateExpression> preStates);
  
	StateExpression assume(StateExpression pre, StateExpressionClosure bool);
	StateExpression assume(StateExpression pre, IRExpression expr);

	StateExpression assign(StateExpression pre, StateExpressionClosure lval, StateExpressionClosure rval);
	StateExpression assign(StateExpression pre, IRExpression lval, IRExpression rval);
  
	StateExpression alloc(StateExpression pre, StateExpressionClosure ptr, StateExpressionClosure size);
	StateExpression alloc(StateExpression pre, IRExpression ptr, IRExpression size);
  
  StateExpression free(StateExpression pre, StateExpressionClosure ptr);
  StateExpression free(StateExpression pre, IRExpression ptr);
  
  StateExpression havoc(StateExpression pre, IRExpression lval);
  StateExpression havoc(StateExpression pre, StateExpressionClosure lval);

  StateExpression call(StateExpression pre, String func, IRExpression ... operands);
  StateExpression call(StateExpression pre, String func, StateExpressionClosure ... operands);
  
	StateExpression declare(StateExpression pre, IRExpression lval);
	StateExpression declare(StateExpression pre, StateExpressionClosure lval);
	
	StateExpression declareEnum(StateExpression pre, IRExpression ... operands);
	StateExpression declareEnum(StateExpression pre, StateExpressionClosure ... operands);
	
  StateExpression emptyState();
  ValidityResult<?> checkAssertion(StateExpression prefix, StateExpressionClosure p) throws PathFactoryException;

  SatResult<?> checkPath(StateExpression prefix) throws PathFactoryException;

  void printCounterExample(PrintStream out, Iterable<?> counterExample) throws PathFactoryException;
}