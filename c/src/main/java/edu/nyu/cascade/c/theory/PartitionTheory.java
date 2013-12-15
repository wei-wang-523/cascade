package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.c.preprocessor.steensgaard.Steensgaard;
import edu.nyu.cascade.ir.expr.BitVectorExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.IRDataFormatter;
import edu.nyu.cascade.ir.expr.IRHeapEncoding;
import edu.nyu.cascade.ir.expr.IROrderMemLayoutEncoding;
import edu.nyu.cascade.ir.expr.IRPartitionHeapEncoder;
import edu.nyu.cascade.ir.expr.IRSoundMemLayoutEncoding;
import edu.nyu.cascade.ir.expr.IntExpressionEncoding;
import edu.nyu.cascade.ir.expr.HeapEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.MultiCellLinearFormatter;
import edu.nyu.cascade.ir.expr.MultiCellSyncFormatter;
import edu.nyu.cascade.ir.expr.OrderLinearMemLayoutEncoding;
import edu.nyu.cascade.ir.expr.PartitionHeapEncoder;
import edu.nyu.cascade.ir.expr.PartitionMemoryModel;
import edu.nyu.cascade.ir.expr.PointerExpressionEncoding;
import edu.nyu.cascade.ir.expr.SingleCellLinearFormatter;
import edu.nyu.cascade.ir.expr.SingleCellSyncFormatter;
import edu.nyu.cascade.ir.expr.SoundLinearMemLayoutEncoding;
import edu.nyu.cascade.ir.expr.SoundSyncMemLayoutEncoding;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class PartitionTheory implements Theory {
  private final ExpressionEncoding encoding;
  private final MemoryModel memoryModel;
  private final Steensgaard.Builder preprocessorBuilder;
  private final CScopeAnalyzer.Builder scopeAnalyzerBuilder;
  
  public PartitionTheory(ExpressionManager exprManager) {
    preprocessorBuilder = new Steensgaard.Builder();
    scopeAnalyzerBuilder = new CScopeAnalyzer.Builder();
    
    IRPartitionHeapEncoder heapEncoder = null;
    
    if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
    	
      IRDataFormatter formatter = null;
    	
    	if(Preferences.isSet(Preferences.OPTION_NON_OVERFLOW)) {
    		encoding = IntExpressionEncoding.create(exprManager);
    		formatter = SingleCellLinearFormatter.create(encoding);
    	} else {
    		encoding = BitVectorExpressionEncoding.create(exprManager);
    		formatter = Preferences.isSet(Preferences.OPTION_MULTI_CELL) ?
        		MultiCellLinearFormatter.create(encoding)
        		: SingleCellLinearFormatter.create(encoding);
    	}
    	
    	IRHeapEncoding heapEncoding = HeapEncoding.create(encoding, formatter);
    	IROrderMemLayoutEncoding memLayout = OrderLinearMemLayoutEncoding
    			.create(heapEncoding);
    	heapEncoder = PartitionHeapEncoder
    			.createOrderEncoding(heapEncoding, memLayout);
    	
    } else { // sound alloc
    	String exprEncoding = Preferences.getString(Preferences.OPTION_MEM_ENCODING);
    	IRHeapEncoding heapEncoding = null;
  		IRDataFormatter formatter = null;
  		IRSoundMemLayoutEncoding memLayout = null;
    	
    	if(Preferences.MEM_ENCODING_SYNC.equals(exprEncoding)) {
    		encoding = PointerExpressionEncoding.create(exprManager);
    		formatter = Preferences.isSet(Preferences.OPTION_MULTI_CELL) ?
        		MultiCellSyncFormatter.create(encoding)
        		: SingleCellSyncFormatter.create(encoding);
        heapEncoding = HeapEncoding.create(encoding, formatter);
        memLayout = SoundSyncMemLayoutEncoding.create(heapEncoding);
        
    	} else {
    		
      	if(Preferences.isSet(Preferences.OPTION_NON_OVERFLOW)) {
      		encoding = IntExpressionEncoding.create(exprManager);
      		formatter = SingleCellLinearFormatter.create(encoding);
      	} else {
      		encoding = BitVectorExpressionEncoding.create(exprManager);
      		formatter = Preferences.isSet(Preferences.OPTION_MULTI_CELL) ?
          		MultiCellLinearFormatter.create(encoding)
          		: SingleCellLinearFormatter.create(encoding);
      	}
      	
      	heapEncoding = HeapEncoding.create(encoding, formatter);
      	memLayout = SoundLinearMemLayoutEncoding.create(heapEncoding);
    	}
    	
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
