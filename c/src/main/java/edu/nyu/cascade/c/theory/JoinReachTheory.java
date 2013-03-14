package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.JoinReachEncoding;
import edu.nyu.cascade.ir.expr.JoinwithQFReachEncoding;
import edu.nyu.cascade.ir.expr.JoinwithRRReachEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProver;

public class JoinReachTheory implements Theory {
  private final JoinReachEncoding encoding;
  private final MemoryModel memoryModel;
  
  public JoinReachTheory(ExpressionManager exprManager) {
    TheoremProver tp = exprManager.getTheoremProver();
    if(tp.getProviderName().equals("cvc4"))
      encoding = new JoinwithRRReachEncoding(exprManager);
    else if(tp.getProviderName().equals("z3"))
      encoding = new JoinwithQFReachEncoding(exprManager);
    else
      throw new IllegalArgumentException("Unsupported theorem prover " + tp);
    memoryModel = JoinReachEncoding.createMemoryModel(encoding);
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
