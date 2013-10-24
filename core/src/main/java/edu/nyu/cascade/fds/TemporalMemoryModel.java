package edu.nyu.cascade.fds;

import xtc.tree.Node;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.AbstractMemoryModel;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
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
    Expression rval = getExpressionEncoding().getIntegerEncoding().unknown();
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
  public BooleanExpression valid(Expression state, Expression ptr, Expression size) {
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
  public Type getStateType() {
    return getExpressionManager().booleanType();
  }
  
  @Override
  public BooleanExpression allocated(Expression state, Expression ptr, Expression size) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("allocated");
  }

  @Override
  public Expression addressOf(Expression content) {
    return content.getChild(1);
  }

  @Override
  public BooleanExpression valid_free(Expression state, Expression ptr) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanExpression valid_malloc(Expression state, Expression ptr,
      Expression size) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression substSizeArr(Expression expr) {
    // TODO Auto-generated method stub
    return null;
  }

	@Override
  public boolean setStateType(Type stateType) {
	  // TODO Auto-generated method stub
	  return false;
  }

	@Override
  public Expression createLval(Expression state, String name,
      IRVarInfo varInfo, Node node) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
  public void setPreProcessor(PreProcessor<?> analyzer) {
	  // TODO Auto-generated method stub
	  
  }

	@Override
  public boolean hasSideEffect() {
	  // TODO Auto-generated method stub
	  return false;
  }

	@Override
  public Expression clearSideEffect(Expression state) {
	  // TODO Auto-generated method stub
	  return null;
  }
}
