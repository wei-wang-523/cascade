package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.c.preprocessor.typeanalysis.TypeAnalyzer;
import edu.nyu.cascade.ir.expr.BurstallMemoryModel;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.IRHeapEncoding;
import edu.nyu.cascade.ir.expr.IROrderMemLayoutEncoding;
import edu.nyu.cascade.ir.expr.IRPartitionHeapEncoder;
import edu.nyu.cascade.ir.expr.IRSoundMemLayoutEncoding;
import edu.nyu.cascade.ir.expr.LinearHeapEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.OrderMemLayoutEncodingFactory;
import edu.nyu.cascade.ir.expr.PartitionHeapEncoder;
import edu.nyu.cascade.ir.expr.PointerExpressionEncoding;
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
    encoding = PointerExpressionEncoding.create(exprManager);
    preprocessorBuilder = new TypeAnalyzer.Builder();
    
    if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
    	IRHeapEncoding heapEncoding = LinearHeapEncoding.create(encoding);
    	IROrderMemLayoutEncoding memLayout = OrderMemLayoutEncodingFactory
    			.create(heapEncoding);
    	heapEncoder = PartitionHeapEncoder.createOrderEncoding(heapEncoding, memLayout);
    } else { // sound alloc
    	String exprEncoding = Preferences.getString(Preferences.OPTION_EXPR_ENCODING);
    	IRHeapEncoding heapEncoding = null;
    	if(Preferences.ENCODING_SYNC.equals(exprEncoding)) {
    		heapEncoding = SynchronousHeapEncoding.create(encoding);
    	} else {
    		heapEncoding = LinearHeapEncoding.create(encoding);
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

}
