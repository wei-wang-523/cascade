package edu.nyu.cascade.c.mode;

import com.google.inject.Inject;

import edu.nyu.cascade.c.pass.alias.steens.Steensgaard;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.expr.BitVectorExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.IRSingleHeapEncoder;
import edu.nyu.cascade.ir.memory.SingleHeapEncoder;
import edu.nyu.cascade.ir.memory.safety.AbstractMemSafetyEncoding;
import edu.nyu.cascade.ir.memory.safety.AbstractStmtMemSafetyEncoding;
import edu.nyu.cascade.ir.memory.safety.IRMemSafetyEncoding;
import edu.nyu.cascade.ir.memory.safety.Strategy;
import edu.nyu.cascade.ir.pass.IRAliasAnalyzer;
import edu.nyu.cascade.ir.state.AbstractStateFactory;
import edu.nyu.cascade.ir.state.HoareStateFactory;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class FlatMode extends AbstractMode {
  private final ExpressionEncoding encoding;
  private StateFactory<?> stateFactory;
  
  @Inject
  public FlatMode(ExpressionManager exprManager) {
  	encoding = BitVectorExpressionEncoding.create(exprManager);
  	
  	Strategy strategy;
  	
  	if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
  		strategy = Strategy.ORDER;
    } else {
  		strategy = Strategy.SOUND;
    }
    
  	IRDataFormatter formatter = getFormatter(encoding);
  	
  	if(Preferences.isSet(Preferences.OPTION_LAMBDA)) {
  		IRMemSafetyEncoding memSafetyEncoding = Preferences.isSet(Preferences.OPTION_STMT) ? 
  				AbstractStmtMemSafetyEncoding.getInstance(encoding, formatter, strategy) :
  					AbstractMemSafetyEncoding.getInstance(encoding, formatter, strategy);
  		
      stateFactory = AbstractStateFactory.createSingleLambda(encoding, formatter, memSafetyEncoding);
  	} else {
    	IRSingleHeapEncoder heapEncoder = SingleHeapEncoder.create(encoding, formatter, strategy);
    	stateFactory = AbstractStateFactory.createSingle(encoding, formatter, heapEncoder);
  	}
  	
  	if(Preferences.isSet(Preferences.OPTION_HOARE)) {
  		stateFactory = HoareStateFactory.create((AbstractStateFactory<?>) stateFactory);
  	}
  }

  @Override
  public ExpressionEncoding getEncoding() {
    return encoding;
  }
	
	@Override
  public StateFactory<?> getStateFactory() {
	  return stateFactory;
  }

	@Override
  public boolean hasPreprocessor() {
	  return true;
  }

	@Override
	public IRAliasAnalyzer<?> buildPreprocessor(SymbolTable symbolTable) {
		IRAliasAnalyzer<?> preProcessor = Steensgaard.create(symbolTable);
		stateFactory.setLabelAnalyzer(preProcessor);
		return preProcessor;
	}
}
