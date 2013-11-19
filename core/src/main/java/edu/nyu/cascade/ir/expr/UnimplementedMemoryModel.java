package edu.nyu.cascade.ir.expr;

import xtc.tree.Node;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.expr.AbstractMemoryModel.MemoryModelType;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.RecordExpression;
import edu.nyu.cascade.prover.TupleExpression;
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
  public Expression addressOf(Expression content) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("addressOf");    
  }

  @Override
  public void setPreProcessor(PreProcessor<?> analyzer) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("setAliasAnalyzer"); 
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
  public Expression substSizeArr(Expression expr) {
    return expr;
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
  public boolean hasSideEffect() {
	  // TODO Auto-generated method stub
	  return false;
  }

	@Override
  public Expression clearSideEffect(Expression state) {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
	public MemoryModelType getType() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public PartitionMemoryModel asPartition() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public FlatMemoryModel asFlat() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BurstallMemoryModel asBurstall() {
		// TODO Auto-generated method stub
		return null;
	}
}
