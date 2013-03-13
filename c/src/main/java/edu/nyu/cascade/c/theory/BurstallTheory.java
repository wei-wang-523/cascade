package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.ir.expr.BurstallMemoryModel;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.PointerExpressionEncoding;
import edu.nyu.cascade.prover.ExpressionManager;

public class BurstallTheory implements Theory {
  private final ExpressionEncoding encoding;
  private final MemoryModel memoryModel;
  
  public BurstallTheory(ExpressionManager exprManager) {
    encoding = PointerExpressionEncoding.create(exprManager, 8);
    memoryModel = BurstallMemoryModel.create(encoding, 8, 8);
  }
  
  public BurstallTheory(ExpressionManager exprManager, int size) {
    encoding = PointerExpressionEncoding.create(exprManager, size);
    memoryModel = BurstallMemoryModel.create(encoding, 8, size);
  }
  
  public BurstallTheory(ExpressionManager exprManager, int size, int length) {
    encoding = PointerExpressionEncoding.create(exprManager, size);
    memoryModel = BurstallMemoryModel.create(encoding, length, size);
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
