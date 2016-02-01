package edu.nyu.cascade.c.mode;

import com.google.inject.Inject;

import edu.nyu.cascade.c.CSymbolTable;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.c.preprocessor.typeanalysis.FSType;
import edu.nyu.cascade.c.preprocessor.typeanalysis.TypeAnalyzer;
import edu.nyu.cascade.ir.expr.BitVectorExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.IntExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.IRPartitionHeapEncoder;
import edu.nyu.cascade.ir.memory.PartitionHeapEncoder;
import edu.nyu.cascade.ir.memory.safety.AbstractMemSafetyEncoding;
import edu.nyu.cascade.ir.memory.safety.IRMemSafetyEncoding;
import edu.nyu.cascade.ir.memory.safety.AbstractMemSafetyEncoding.Strategy;
import edu.nyu.cascade.ir.state.AbstractStateFactory;
import edu.nyu.cascade.ir.state.HoareStateFactory;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class BurstallMode extends AbstractMode {
  private final ExpressionEncoding encoding;
  private StateFactory<FSType> stateFactory;
  
  @Inject
  public BurstallMode(ExpressionManager exprManager) {
  	if(Preferences.isSet(Preferences.OPTION_NON_OVERFLOW)) {
  		encoding = IntExpressionEncoding.create(exprManager);
  	} else {
  		encoding = BitVectorExpressionEncoding.create(exprManager);
  	}
  	
    Strategy strategy;
    
  	if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
  		strategy = Strategy.ORDER;
    } else { // sound alloc
  		strategy = Strategy.SOUND;
    }
  	
  	IRDataFormatter formatter = getFormatter(encoding);
  	
  	if(Preferences.isSet(Preferences.OPTION_LAMBDA)) {
      IRMemSafetyEncoding memSafetyEncoding = AbstractMemSafetyEncoding
      		.getInstance(encoding, formatter, strategy);
      
      stateFactory = AbstractStateFactory.createMultipleLambda(encoding, formatter, memSafetyEncoding);
  	} else {
    	IRPartitionHeapEncoder heapEncoder = PartitionHeapEncoder.create(encoding, formatter, strategy);
    	
      stateFactory = AbstractStateFactory.createMultiple(encoding, formatter, heapEncoder);
  	}
  	
  	if(Preferences.isSet(Preferences.OPTION_HOARE)) {
  		stateFactory = HoareStateFactory.create((AbstractStateFactory<FSType>) stateFactory);
  	}
  }
  
  @Override
  public ExpressionEncoding getEncoding() {
    return encoding;
  }

	@Override
  public StateFactory<FSType> getStateFactory() {
	  return stateFactory;
  }

	@Override
  public boolean hasPreprocessor() {
	  return true;
  }

	@Override
  public PreProcessor<FSType> buildPreprocessor(CSymbolTable symbolTable) {
		PreProcessor<FSType> preProcessor = TypeAnalyzer.create();
		stateFactory.setLabelAnalyzer(preProcessor);
		return preProcessor;
  }
}