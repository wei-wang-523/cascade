package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.LoLLiwithQFReachEncoding;
import edu.nyu.cascade.ir.expr.LoLLiwithRRReachEncoding;
import edu.nyu.cascade.ir.expr.ReachMemoryModel;
import edu.nyu.cascade.ir.expr.ReachEncoding;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProver;

public class LoLLiReachTheory implements Theory {
  private final ReachEncoding encoding;
  private final ReachMemoryModel memoryModel;
  
  public LoLLiReachTheory(ExpressionManager exprManager) {
    TheoremProver tp = exprManager.getTheoremProver();
    if(tp.getProviderName().equals("cvc4")) {
      encoding = new LoLLiwithRRReachEncoding(exprManager);
      memoryModel = LoLLiwithRRReachEncoding.createMemoryModel(encoding);
    } else if(tp.getProviderName().equals("z3")) {
      encoding = new LoLLiwithQFReachEncoding(exprManager);
      memoryModel = LoLLiwithQFReachEncoding.createMemoryModel(encoding);
    } else
      throw new IllegalArgumentException("Unsupported theorem prover " + tp);
  }

  @Override
  public ExpressionEncoding getEncoding() {
    return encoding;
  }

  @Override
  public ReachMemoryModel getMemoryModel() {
    return memoryModel;
  }
}
