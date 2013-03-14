package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.ir.expr.LISBQwithQFReachEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.LISBQwithRRReachEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProver;

public class LISBQReachTheory implements Theory {
  private final ExpressionEncoding encoding;
  private final MemoryModel memoryModel;
  
  public LISBQReachTheory(ExpressionManager exprManager) {
    TheoremProver tp = exprManager.getTheoremProver();
    if(tp.getProviderName().equals("cvc4"))
      encoding = new LISBQwithRRReachEncoding(exprManager);
    else if(tp.getProviderName().equals("z3"))
      encoding = new LISBQwithQFReachEncoding(exprManager);
    else
      throw new IllegalArgumentException("Unsupported theorem prover " + tp);
    memoryModel = LISBQwithQFReachEncoding.createMemoryModel(encoding);
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
