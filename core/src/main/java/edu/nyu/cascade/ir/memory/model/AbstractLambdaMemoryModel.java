package edu.nyu.cascade.ir.memory.model;

//import java.util.List;

import com.google.inject.Inject;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.ExpressionManager;

public abstract class AbstractLambdaMemoryModel<T> implements MemoryModel<T> {
  
  private final StateFactory<T> stateFactory;
  
  @Inject
  protected AbstractLambdaMemoryModel(StateFactory<T> stateFactory) {
    this.stateFactory = stateFactory;
  }

  @Override
  public ExpressionEncoding getExpressionEncoding() {
    return stateFactory.getExpressionEncoding();
  }
  
  @Override
  public IRDataFormatter getDataFormatter() {
  	return stateFactory.getDataFormatter();
  }
  
  @Override
  public StateFactory<T> getStateFactory() {
  	return stateFactory;
  }

  @Override
  public ExpressionManager getExpressionManager() {
    return getExpressionEncoding().getExpressionManager();
  }
	
	@Override
	public <X> void setPreProcessor(PreProcessor<X> analyzer) {
		throw new UnsupportedOperationException("Not supported in lambda memory model");
	}
}
