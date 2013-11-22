package edu.nyu.cascade.datatypes;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.c.preprocessor.PreProcessor.Builder;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.FlatMemoryModel;
import edu.nyu.cascade.ir.expr.IRHeapEncoding;
import edu.nyu.cascade.ir.expr.IRSingleHeapEncoder;
import edu.nyu.cascade.ir.expr.IRSoundMemLayoutEncoding;
import edu.nyu.cascade.ir.expr.LinearHeapEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.PartitionHeapEncoder;
import edu.nyu.cascade.ir.expr.SingleHeapEncoderAdapter;
import edu.nyu.cascade.ir.expr.SoundMemLayoutEncodingFactory;
import edu.nyu.cascade.prover.ExpressionManager;

public class CompressedDomainNames implements Theory {
  private final CompressedDomainNamesEncoding encoding;
  private final IRSingleHeapEncoder heapEncoder;
  private final MemoryModel memoryModel;
  
  public CompressedDomainNames(ExpressionManager exprManager) {
    String tpProviderName = exprManager.getTheoremProver().getProviderName();
    if("z3".equals(tpProviderName))
      encoding = CompressedDomainNamesEncoding_Z3.create(exprManager);
    else if ("cvc4".equals(tpProviderName))
      encoding = CompressedDomainNamesEncoding_CVC4.create(exprManager);
    else
      throw new IllegalArgumentException("Unknown theorem prover " + tpProviderName);
    
    PartitionHeapEncoder parHeapEncoder = null;
   
    IRHeapEncoding heapEncoding = LinearHeapEncoding.create(encoding);
    IRSoundMemLayoutEncoding memLayout = SoundMemLayoutEncodingFactory
    		.create(heapEncoding);
    parHeapEncoder = PartitionHeapEncoder
    		.createSoundEncoding(heapEncoding, memLayout);
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

	@Override
  public Builder<?> getPreprocessorBuilder() {
	  // TODO Auto-generated method stub
	  return null;
  }

	@Override
	public CScopeAnalyzer.Builder getScopeAnalyzerBuilder() {
		// TODO Auto-generated method stub
		return null;
	}

}
