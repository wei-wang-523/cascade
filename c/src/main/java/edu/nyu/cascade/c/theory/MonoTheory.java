package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.ir.expr.MonolithicExtendMemoryModel;
import edu.nyu.cascade.ir.expr.MonolithicMemoryModel;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.PointerExpressionEncoding;
import edu.nyu.cascade.prover.ExpressionManager;

public class MonoTheory implements Theory {
  private final ExpressionEncoding encoding;
  private final MemoryModel memoryModel;
  
  public MonoTheory(ExpressionManager exprManager) {
    encoding = PointerExpressionEncoding.create(exprManager);
    memoryModel = MonolithicMemoryModel.create(encoding);
  }
  
/*  public MonolithicTheory(ExpressionManager exprManager, int size) {
    encoding = PointerExpressionEncoding.create(exprManager, size);
    memoryModel = MonolithicMemoryModel.create(encoding, 8, size);
  }
  
  public MonolithicTheory(ExpressionManager exprManager, int size, int length) {
    encoding = PointerExpressionEncoding.create(exprManager, size);
    memoryModel = MonolithicMemoryModel.create(encoding, length, size);
  }*/

  @Override
  public ExpressionEncoding getEncoding() {
    return encoding;
  }

  @Override
  public MemoryModel getMemoryModel() {
    return memoryModel;
  }

}
