package edu.nyu.cascade.datatypes;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.ir.expr.BitVectorMemoryModel;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.prover.ExpressionManager;

public class CompressedDomainNames implements Theory {
  private final CompressedDomainNamesEncoding encoding;
  private final MemoryModel memoryModel;
  
  public CompressedDomainNames(ExpressionManager exprManager) {
    if(exprManager instanceof edu.nyu.cascade.z3.ExpressionManagerImpl)
      encoding = new CompressedDomainNamesEncoding_Z3(exprManager);
    else // if (exprManager instanceof edu.nyu.cascade.cvc4.ExpressionManagerImpl)
      encoding = new CompressedDomainNamesEncoding_CVC4(exprManager);
    
    memoryModel = BitVectorMemoryModel.create(encoding,
        encoding.getAddressSize(), encoding.getWordSize());
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
