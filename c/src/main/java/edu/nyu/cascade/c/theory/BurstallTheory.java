package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.c.preprocessor.typeanalysis.TypeAnalyzer;
import edu.nyu.cascade.ir.expr.BitVectorExpressionEncoding;
import edu.nyu.cascade.ir.expr.BurstallMemoryModel;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.IRDataFormatter;
import edu.nyu.cascade.ir.expr.IRHeapEncoding;
import edu.nyu.cascade.ir.expr.IROrderMemLayoutEncoding;
import edu.nyu.cascade.ir.expr.IRPartitionHeapEncoder;
import edu.nyu.cascade.ir.expr.IRSoundMemLayoutEncoding;
import edu.nyu.cascade.ir.expr.IntExpressionEncoding;
import edu.nyu.cascade.ir.expr.LinearHeapEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.MultiCellFormatter;
import edu.nyu.cascade.ir.expr.OrderMemLayoutEncodingFactory;
import edu.nyu.cascade.ir.expr.PartitionHeapEncoder;
import edu.nyu.cascade.ir.expr.PointerExpressionEncoding;
import edu.nyu.cascade.ir.expr.SingleCellFormatter;
import edu.nyu.cascade.ir.expr.SoundMemLayoutEncodingFactory;
import edu.nyu.cascade.ir.expr.SynchronousHeapEncoding;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class BurstallTheory implements Theory {
  private final ExpressionEncoding encoding;
  private final IRPartitionHeapEncoder heapEncoder;
  private final MemoryModel memoryModel;
  private final TypeAnalyzer.Builder preprocessorBuilder;
  
  public BurstallTheory(ExpressionManager exprManager) {
    preprocessorBuilder = new TypeAnalyzer.Builder();
    
    if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
    	if(Preferences.isSet(Preferences.OPTION_NON_OVERFLOW)) {
    		encoding = IntExpressionEncoding.create(exprManager);
    	} else {
    		encoding = BitVectorExpressionEncoding.create(exprManager);
    	}
    	      
      IRDataFormatter formatter = Preferences.isSet(Preferences.OPTION_MULTI_CELL) ?
      		MultiCellFormatter.create(encoding)
      		: SingleCellFormatter.create(encoding);
    	
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
      	      
        IRDataFormatter formatter = Preferences.isSet(Preferences.OPTION_MULTI_CELL) ?
        		MultiCellFormatter.create(encoding)
        		: SingleCellFormatter.create(encoding);
      	
        heapEncoding = LinearHeapEncoding.create(encoding, formatter);
    	}
    	
    	IRSoundMemLayoutEncoding memLayout = SoundMemLayoutEncodingFactory
    			.create(heapEncoding);
    	heapEncoder = PartitionHeapEncoder.createSoundEncoding(heapEncoding, memLayout);
    }
    
  	memoryModel = BurstallMemoryModel.create(encoding, heapEncoder);	
  }

  @Override
  public TypeAnalyzer.Builder getPreprocessorBuilder() {
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
		// TODO Auto-generated method stub
		return null;
	}

}
