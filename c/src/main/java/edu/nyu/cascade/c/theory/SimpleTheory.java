package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.ir.expr.BitVectorExpressionEncoding;
import edu.nyu.cascade.ir.expr.SimpleMemoryModel;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.prover.ExpressionManager;

public class SimpleTheory implements Theory {
  private final ExpressionEncoding encoding;
  private final MemoryModel memoryModel;
  
  public SimpleTheory(ExpressionManager exprManager) {
    encoding = BitVectorExpressionEncoding.create(exprManager, 8);
    memoryModel = SimpleMemoryModel.create(encoding, 8);
  }
  
  public SimpleTheory(ExpressionManager exprManager, int size) {
    encoding = BitVectorExpressionEncoding.create(exprManager, size);
    memoryModel = SimpleMemoryModel.create(encoding, size);
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
