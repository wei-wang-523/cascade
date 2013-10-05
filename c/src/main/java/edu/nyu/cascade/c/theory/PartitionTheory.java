package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.PartitionMemoryModelOrder;
import edu.nyu.cascade.ir.expr.PartitionMemoryModelSound;
import edu.nyu.cascade.ir.expr.PointerExpressionEncoding;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class PartitionTheory implements Theory {
  private final ExpressionEncoding encoding;
  private final MemoryModel memoryModel;
  
  public PartitionTheory(ExpressionManager exprManager) {
    encoding = PointerExpressionEncoding.create(exprManager);
    if(Preferences.isSet(Preferences.OPTION_ORDER_ALLOC))
    	memoryModel = PartitionMemoryModelOrder.create(encoding);
    else
    	memoryModel = PartitionMemoryModelSound.create(encoding);	
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
