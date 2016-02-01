package edu.nyu.cascade.ir.memory.model;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateExpressionClosure;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;

public class UnimplementedMemoryModel<T> implements MemoryModel<T> {

	@Override
  public BooleanExpression validAccess(StateExpression state, Expression ptr) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public BooleanExpression validAccessRange(StateExpression state, Expression ptr,
      Expression size) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public StateExpression assign(StateExpression state, Expression lval,
      Expression rval) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public Expression deref(StateExpression state, Expression p) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public StateExpressionClosure suspend(StateExpression state, Expression expr) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public StateExpression alloc(StateExpression state, Expression ptr,
      Expression size) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public StateExpression free(StateExpression state, Expression ptr) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public StateExpression havoc(StateExpression state, Expression lval) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public ExpressionEncoding getExpressionEncoding() {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public ExpressionManager getExpressionManager() {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public Expression createLval(String name) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public <X> void setPreProcessor(PreProcessor<X> analyzer) {
	  // TODO Auto-generated method stub
  }

	@Override
  public BooleanExpression validFree(StateExpression state, Expression ptr) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public BooleanExpression validMalloc(StateExpression state, Expression ptr,
      Expression size) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public StateFactory<T> getStateFactory() {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public IRDataFormatter getDataFormatter() {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public StateExpression declare(StateExpression state, Expression lval, IRVarInfo info) {
	  // TODO Auto-generated method stub
	  return null;
  }
}
