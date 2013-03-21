package edu.nyu.cascade.fds;

import com.google.inject.internal.Preconditions;

import edu.nyu.cascade.ir.expr.AbstractMemoryModel;
import edu.nyu.cascade.ir.expr.ExpressionClosure;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public class TemporalMemoryModel extends AbstractMemoryModel {

  public TemporalMemoryModel(ExpressionEncoding encoding) {
    super(encoding);
  }

  @Override
  public StateProperty assign(Expression state,
      Expression lval,
      Expression rval) {
    Preconditions.checkArgument( state.isBoolean() );
    Preconditions.checkArgument(lval.isVariable());
    Preconditions.checkArgument(rval.getType().equals( lval.getType() ) );
    
    Expression newVar = getExpressionManager().variable(
        lval.asVariable().getName(), lval.getType(), true);
    
    return StatePropertyImpl.valueOf(state.subst(lval, newVar)
        .asBooleanExpression().and(lval.eq(rval.subst(lval, newVar))));
  }
  
  @Override
  public StateProperty havoc(Expression state,
      Expression lval) {
    Preconditions.checkArgument( state.isBoolean() );
    Preconditions.checkArgument(lval.isVariable());
    
    Expression newVar = getExpressionManager().variable(
        lval.asVariable().getName(), lval.getType(), true);
    Expression rval = getExpressionEncoding().unknown();
    return StatePropertyImpl.valueOf(state.subst(lval, newVar)
        .asBooleanExpression().and(lval.eq(rval.subst(lval, newVar))));
  }

  @Override
  public Expression deref(Expression state, Expression p) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("deref");
  }

  @Override
  public BooleanExpression valid(Expression state, Expression ptr) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("valid");
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
  public void addLval(VariableExpression p) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("addLval");
  }

  @Override
  public Type getStateType() {
    return getExpressionManager().booleanType();
  }
  
  @Override
  public Type getMemoryType() {
    return getExpressionManager().booleanType();
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
