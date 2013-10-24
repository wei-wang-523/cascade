package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.c.preprocessor.PreProcessor.Builder;
import edu.nyu.cascade.ir.expr.BurstallMemoryModelSync;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.PointerExpressionEncoding;
import edu.nyu.cascade.prover.ExpressionManager;

public class BurstallSyncTheory implements Theory {
  private final ExpressionEncoding encoding;
  private final MemoryModel memoryModel;
  
  public BurstallSyncTheory(ExpressionManager exprManager) {
    encoding = PointerExpressionEncoding.create(exprManager);
    memoryModel = BurstallMemoryModelSync.create(encoding);
  }

  @Override
  public ExpressionEncoding getEncoding() {
    return encoding;
  }

  @Override
  public MemoryModel getMemoryModel() {
    return memoryModel;
  }

	@Override
  public Builder<?> getPreprocessorBuilder() {
	  // TODO Auto-generated method stub
	  return null;
  }

}
