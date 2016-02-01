package edu.nyu.cascade.c.mode;

import com.google.inject.Inject;

import edu.nyu.cascade.c.CSymbolTable;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.expr.BitVectorExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.IntExpressionEncoding;
import edu.nyu.cascade.ir.expr.PointerExpressionEncoding;
import edu.nyu.cascade.ir.formatter.IRDataFormatter;
import edu.nyu.cascade.ir.memory.IRSingleHeapEncoder;
import edu.nyu.cascade.ir.memory.SingleHeapEncoder;
import edu.nyu.cascade.ir.memory.model.LambdaFlatMemoryModel;
import edu.nyu.cascade.ir.memory.model.MemoryModel;
import edu.nyu.cascade.ir.memory.safety.AbstractMemSafetyEncoding;
import edu.nyu.cascade.ir.memory.safety.IRMemSafetyEncoding;
import edu.nyu.cascade.ir.memory.safety.AbstractMemSafetyEncoding.Strategy;
import edu.nyu.cascade.ir.state.AbstractStateFactory;
import edu.nyu.cascade.ir.state.HoareStateFactory;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class FlatMode extends AbstractMode {
  private final ExpressionEncoding encoding;
  private final MemoryModel<?> memoryModel;
  private StateFactory<?> stateFactory;
  
  @Inject
  public FlatMode(ExpressionManager exprManager) {
  	
  	Strategy strategy;
  	
  	if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
  		strategy = Strategy.ORDER_LINEAR;
  		
    	if(Preferences.isSet(Preferences.OPTION_NON_OVERFLOW)) {
    		encoding = IntExpressionEncoding.create(exprManager);
    	} else {
    		encoding = BitVectorExpressionEncoding.create(exprManager);
    	}
    	
    } else {
    	String exprEncoding = Preferences.getString(Preferences.OPTION_MEM_ENCODING);
    	
    	if(Preferences.MEM_ENCODING_SYNC.equals(exprEncoding)) {
    		strategy = Strategy.SOUND_SYNC;
    		
    		encoding = PointerExpressionEncoding.create(exprManager);
    	} else {
    		strategy = Strategy.SOUND_LINEAR;
    		
    		if(Preferences.isSet(Preferences.OPTION_NON_OVERFLOW)) {
      		encoding = IntExpressionEncoding.create(exprManager);
      	} else {
      		encoding = BitVectorExpressionEncoding.create(exprManager);
      	}
    	}
    }
    
  	IRDataFormatter formatter = getFormatter(encoding);
  	
  	if(Preferences.isSet(Preferences.OPTION_LAMBDA)) {
      IRMemSafetyEncoding memSafetyEncoding = AbstractMemSafetyEncoding
      		.getInstance(encoding, formatter, strategy);
      stateFactory = AbstractStateFactory.createSingleLambda(encoding, formatter, memSafetyEncoding);
  	} else {
    	IRSingleHeapEncoder heapEncoder = SingleHeapEncoder.create(encoding, formatter, strategy);
    	stateFactory = AbstractStateFactory.createSingle(encoding, formatter, heapEncoder);
  	}
  	
  	if(Preferences.isSet(Preferences.OPTION_HOARE)) {
  		stateFactory = HoareStateFactory.create((AbstractStateFactory<?>) stateFactory);
  	}
  	
  	memoryModel = LambdaFlatMemoryModel.create(stateFactory);
  }

  @Override
  public ExpressionEncoding getEncoding() {
    return encoding;
  }

  @Override
  public MemoryModel<?> getMemoryModel() {
    return memoryModel;
  }
	
	@Override
  public StateFactory<?> getStateFactory() {
	  return stateFactory;
  }

	@Override
  public boolean hasPreprocessor() {
	  return false;
  }

	@Override
  public PreProcessor<?> buildPreprocessor(CSymbolTable symbolTable) {
	  throw new UnsupportedOperationException("Flat mode doesn't have preprocessor.");
  }
}
