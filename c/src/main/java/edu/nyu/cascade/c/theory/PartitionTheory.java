package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.ir.expr.PartitionMemoryModel;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.PointerExpressionEncoding;
import edu.nyu.cascade.prover.ExpressionManager;

public class PartitionTheory implements Theory {
  private final ExpressionEncoding encoding;
  private final MemoryModel memoryModel;
  
  public PartitionTheory(ExpressionManager exprManager) {
    encoding = PointerExpressionEncoding.create(exprManager);
    memoryModel = PartitionMemoryModel.create(encoding);
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
