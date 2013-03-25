package edu.nyu.cascade.ir.expr;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public class UnimplementedMemoryModel implements MemoryModel {

  @Override
  public Expression assign(Expression state, Expression lval,
      Expression rval) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("assign");
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("deref");
  }

  @Override
  public Expression freshState() {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("freshState");
  }
  
  @Override
  public Expression havoc(Expression state, Expression lval) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("havoc");
  }

  @Override
  public ImmutableSet<BooleanExpression> getAssumptions(Expression state) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("getAssumptions");
  }

  @Override
  public ExpressionEncoding getExpressionEncoding() {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("getExpressionEncoding");
  }

  @Override
  public ExpressionManager getExpressionManager() {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("getExpressionManager");
  }

  @Override
  public Type getStateType() {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("getStateType");
  }
  
  @Override
  public Type getMemoryType() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ExpressionClosure suspend(Expression memory, Expression expr) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("suspend");
  }

  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("valid");
  }
  
  @Override
  public void addLval(VariableExpression p) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("addLval");
  }
  
  @Override
  public Expression initialState() {
    // TODO Auto-generated method stub
    return null;
  }
  
  @Override
  public BooleanExpression alloc(Expression state, Expression ptr, Expression size) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("alloc");
  }

  @Override
  public BooleanExpression declareStruct(Expression state, Expression ptr, Expression size) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("declareStruct");
  }
  
  @Override
  public BooleanExpression declareArray(Expression state, Expression ptr, Expression size) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("declareArray");
  }
  
  @Override
  public BooleanExpression free(Expression state, Expression ptr) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("free");
  }

  @Override
  public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("allocated");
  }

  @Override
  public ExpressionClosure getCurrentState() {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("getCurrentState");
  }
  
  @Override
  public void resetCurrentState() {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("resetCurrentState");    
  }
}