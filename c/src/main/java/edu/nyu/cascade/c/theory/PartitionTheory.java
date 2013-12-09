package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.c.preprocessor.steensgaard.Steensgaard;
import edu.nyu.cascade.ir.expr.BitVectorExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.IRBVDataFormatter;
import edu.nyu.cascade.ir.expr.IRHeapEncoding;
import edu.nyu.cascade.ir.expr.IROrderMemLayoutEncoding;
import edu.nyu.cascade.ir.expr.IRPartitionHeapEncoder;
import edu.nyu.cascade.ir.expr.IRSoundMemLayoutEncoding;
import edu.nyu.cascade.ir.expr.IntExpressionEncoding;
import edu.nyu.cascade.ir.expr.LinearHeapEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.MultiCellBVFormatter;
import edu.nyu.cascade.ir.expr.OrderMemLayoutEncodingFactory;
import edu.nyu.cascade.ir.expr.PartitionHeapEncoder;
import edu.nyu.cascade.ir.expr.PartitionMemoryModel;
import edu.nyu.cascade.ir.expr.PointerExpressionEncoding;
import edu.nyu.cascade.ir.expr.SingleCellBVFormatter;
import edu.nyu.cascade.ir.expr.SoundMemLayoutEncodingFactory;
import edu.nyu.cascade.ir.expr.SynchronousHeapEncoding;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class PartitionTheory implements Theory {
  private final ExpressionEncoding encoding;
  private final IRPartitionHeapEncoder heapEncoder;
  private final MemoryModel memoryModel;
  private final Steensgaard.Builder preprocessorBuilder;
  private final CScopeAnalyzer.Builder scopeAnalyzerBuilder;
  
  public PartitionTheory(ExpressionManager exprManager) {
    preprocessorBuilder = new Steensgaard.Builder();
    scopeAnalyzerBuilder = new CScopeAnalyzer.Builder();
    
    if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
    	if(Preferences.isSet(Preferences.OPTION_NON_OVERFLOW)) {
    		encoding = IntExpressionEncoding.create(exprManager);
    	} else {
    		encoding = BitVectorExpressionEncoding.create(exprManager);
    	}
    	      
      IRBVDataFormatter formatter = Preferences.isSet(Preferences.OPTION_MULTI_CELL) ?
      		MultiCellBVFormatter.create(encoding)
      		: SingleCellBVFormatter.create(encoding);
    	
    	IRHeapEncoding heapEncoding = LinearHeapEncoding.create(encoding, formatter);
    	IROrderMemLayoutEncoding memLayout = OrderMemLayoutEncodingFactory
    			.create(heapEncoding);
    	heapEncoder = PartitionHeapEncoder
    			.createOrderEncoding(heapEncoding, memLayout);
    	
    } else { // sound alloc
    	String exprEncoding = Preferences.getString(Preferences.OPTION_MEM_ENCODING);
    	IRHeapEncoding heapEncoding = null;
    	if(Preferences.MEM_ENCODING_SYNC.equals(exprEncoding)) {
    		encoding = PointerExpressionEncoding.create(exprManager);
    		heapEncoding = SynchronousHeapEncoding.create(encoding);
    	} else {
    		if(Preferences.isSet(Preferences.OPTION_NON_OVERFLOW)) {
      		encoding = IntExpressionEncoding.create(exprManager);
      	} else {
      		encoding = BitVectorExpressionEncoding.create(exprManager);
      	}
      	      
        IRBVDataFormatter formatter = Preferences.isSet(Preferences.OPTION_MULTI_CELL) ?
        		MultiCellBVFormatter.create(encoding)
        		: SingleCellBVFormatter.create(encoding);
      	
        heapEncoding = LinearHeapEncoding.create(encoding, formatter);
    	}
    	
    	IRSoundMemLayoutEncoding memLayout = SoundMemLayoutEncodingFactory
    			.create(heapEncoding);
    	heapEncoder = PartitionHeapEncoder.createSoundEncoding(heapEncoding, memLayout);
    }
  	memoryModel = PartitionMemoryModel.create(encoding, heapEncoder);	
  }

  @Override
  public Steensgaard.Builder getPreprocessorBuilder() {
  	return preprocessorBuilder;
  }
  
  @Override
  public ExpressionEncoding getEncoding() {
    return encoding;
  }

  @Override
  public MemoryModel getMemoryModel() {
    return memoryModel;
  }

	@Override
	public CScopeAnalyzer.Builder getScopeAnalyzerBuilder() {
		return scopeAnalyzerBuilder;
	}
}
