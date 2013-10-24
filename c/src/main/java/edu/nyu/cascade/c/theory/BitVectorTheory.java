package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.c.preprocessor.PreProcessor.Builder;
import edu.nyu.cascade.ir.expr.BitVectorExpressionEncoding;
import edu.nyu.cascade.ir.expr.BitVectorMemoryModelOrder;
import edu.nyu.cascade.ir.expr.BitVectorMemoryModelSound;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class BitVectorTheory implements Theory {
  private final ExpressionEncoding encoding;
  private final MemoryModel memoryModel;
  
  public BitVectorTheory(ExpressionManager exprManager) {
    encoding = BitVectorExpressionEncoding.create(exprManager);
    if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC))
    	memoryModel = BitVectorMemoryModelOrder.create(encoding);
    else
    	memoryModel = BitVectorMemoryModelSound.create(encoding);
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
