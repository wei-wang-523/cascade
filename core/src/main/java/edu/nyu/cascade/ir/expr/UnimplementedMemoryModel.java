package edu.nyu.cascade.ir.expr;

import xtc.tree.Node;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.c.preprocessor.AliasAnalysis;
import edu.nyu.cascade.c.preprocessor.TypeCastAnalysis;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TupleExpression;
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
  public BooleanExpression valid(Expression state, Expression ptr, Expression size) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("valid");
  }
  
  @Override
  public VariableExpression createLval(String prefix, Node node) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("createLval");
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
  public void clearCurrentState() {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("clearCurrentState");    
  }

  @Override
  public Expression addressOf(Expression content) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("addressOf");    
  }

  @Override
  public void setAliasAnalyzer(AliasAnalysis analyzer) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("setAliasAnalyzer"); 
  }
  
  @Override
  public void setTypeCastAnalyzer(TypeCastAnalysis analyzer) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("setTypeCastAnalyzer"); 
  }

  @Override
  public BooleanExpression valid_free(Expression state, Expression ptr) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("valid_free"); 
  }

  @Override
  public BooleanExpression valid_malloc(Expression state, Expression ptr,
      Expression size) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("valid_malloc"); 
  }
  
  @Override
  public Expression substAlloc(Expression expr) {
    return expr;
  }

  @Override
  public Type getAllocType() {
    // TODO Auto-generated method stub
    return null;
  }

	@Override
	public Expression combineRecordStates(BooleanExpression guard,
			RecordExpression rec_1, RecordExpression rec_0) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public TupleExpression getUpdatedState(Expression state, Expression... elems) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public TupleExpression getUpdatedState(Expression state,
			Iterable<Expression> elems) {
		// TODO Auto-generated method stub
		return null;
	}
}
