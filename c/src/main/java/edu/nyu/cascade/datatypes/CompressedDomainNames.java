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
    String tpProviderName = exprManager.getTheoremProver().getProviderName();
    if("z3".equals(tpProviderName))
      encoding = new CompressedDomainNamesEncoding_Z3(exprManager);
    else if ("cvc4".equals(tpProviderName))
      encoding = new CompressedDomainNamesEncoding_CVC4(exprManager);
    else
      throw new IllegalArgumentException("Unknown theorem prover " + tpProviderName);
    memoryModel = BitVectorMemoryModel.create(encoding);
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
