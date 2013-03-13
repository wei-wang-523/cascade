package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.ir.expr.BitVectorExpressionEncoding;
import edu.nyu.cascade.ir.expr.BitVectorMemoryModel;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.prover.ExpressionManager;

public class BitVectorTheory implements Theory {
  private final ExpressionEncoding encoding;
  private final MemoryModel memoryModel;
  
  public BitVectorTheory(ExpressionManager exprManager) {
    encoding = BitVectorExpressionEncoding.create(exprManager, 8);
    memoryModel = BitVectorMemoryModel.create(encoding, 8, 8);
  }
  
  public BitVectorTheory(ExpressionManager exprManager, int size) {
    encoding = BitVectorExpressionEncoding.create(exprManager, size);
    memoryModel = BitVectorMemoryModel.create(encoding, 8, size);
  }
  
  public BitVectorTheory(ExpressionManager exprManager, int size, int length) {
    encoding = BitVectorExpressionEncoding.create(exprManager, size);
    memoryModel = BitVectorMemoryModel.create(encoding, length, size);
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
