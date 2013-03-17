package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.ir.expr.LISBQExdReachEncoding;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.prover.ExpressionManager;

public class LISBQExdReachTheory implements Theory {
  private final LISBQExdReachEncoding encoding;
  private final MemoryModel memoryModel;
  
  public LISBQExdReachTheory(ExpressionManager exprManager) {
    encoding = new LISBQExdReachEncoding(exprManager);
    memoryModel = LISBQExdReachEncoding.createMemoryModel(encoding);
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
