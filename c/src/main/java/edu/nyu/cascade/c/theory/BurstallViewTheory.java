package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.ir.expr.BurstallView2MemoryModel;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.PointerExpressionEncoding;
import edu.nyu.cascade.prover.ExpressionManager;

public class BurstallViewTheory implements Theory {
  private final ExpressionEncoding encoding;
  private final MemoryModel memoryModel;
  
  public BurstallViewTheory(ExpressionManager exprManager) {
    encoding = PointerExpressionEncoding.create(exprManager);
    memoryModel = BurstallView2MemoryModel.create(encoding);
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
