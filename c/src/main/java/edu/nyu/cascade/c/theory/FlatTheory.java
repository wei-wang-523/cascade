package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.FlatMemoryModel;
import edu.nyu.cascade.ir.expr.IRHeapEncoding;
import edu.nyu.cascade.ir.expr.IROrderMemLayoutEncoding;
import edu.nyu.cascade.ir.expr.IRSingleHeapEncoder;
import edu.nyu.cascade.ir.expr.IRSoundMemLayoutEncoding;
import edu.nyu.cascade.ir.expr.LinearHeapEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.OrderMemLayoutEncodingFactory;
import edu.nyu.cascade.ir.expr.PartitionHeapEncoder;
import edu.nyu.cascade.ir.expr.PointerExpressionEncoding;
import edu.nyu.cascade.ir.expr.SingleHeapEncoderAdapter;
import edu.nyu.cascade.ir.expr.SoundMemLayoutEncodingFactory;
import edu.nyu.cascade.ir.expr.SynchronousHeapEncoding;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class FlatTheory implements Theory {
  private final ExpressionEncoding encoding;
  private final IRSingleHeapEncoder heapEncoder;
  private final MemoryModel memoryModel;
  
  public FlatTheory(ExpressionManager exprManager) {
    encoding = PointerExpressionEncoding.create(exprManager);
    PartitionHeapEncoder parHeapEncoder = null;
    
    if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC)) {
    	IRHeapEncoding heapEncoding = LinearHeapEncoding.create(encoding);
    	IROrderMemLayoutEncoding memLayout = OrderMemLayoutEncodingFactory
    			.create(heapEncoding);
    	parHeapEncoder = PartitionHeapEncoder
    			.createOrderEncoding(heapEncoding, memLayout);
    } else {
    	IRHeapEncoding heapEncoding = LinearHeapEncoding.create(encoding);
    	IRHeapEncoding heapEncoding_sync = SynchronousHeapEncoding.create(encoding);
    	IRSoundMemLayoutEncoding memLayout = SoundMemLayoutEncodingFactory
    			.create(heapEncoding_sync);
    	parHeapEncoder = PartitionHeapEncoder
    			.createSoundEncoding(heapEncoding_sync, memLayout);
    }
    heapEncoder = SingleHeapEncoderAdapter.create(parHeapEncoder);
  	memoryModel = FlatMemoryModel.create(encoding, heapEncoder);	
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
