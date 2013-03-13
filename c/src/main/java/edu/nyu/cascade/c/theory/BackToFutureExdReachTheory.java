package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.ir.expr.BackToFutureExdReachEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.prover.ExpressionManager;

public class BackToFutureExdReachTheory implements Theory {
  private final BackToFutureExdReachEncoding encoding;
  private final MemoryModel memoryModel;
  
  public BackToFutureExdReachTheory(ExpressionManager exprManager) {
    encoding = new BackToFutureExdReachEncoding(exprManager);
    memoryModel = BackToFutureExdReachEncoding.createMemoryModel(encoding);
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
