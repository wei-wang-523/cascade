package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.ir.expr.LoLLiwithQFDArrReachEncoding;
import edu.nyu.cascade.ir.expr.ReachMemoryModel;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class LoLLiDArrReachTheory implements Theory {
  private final LoLLiwithQFDArrReachEncoding encoding;
  private final ReachMemoryModel memoryModel;
  
  public LoLLiDArrReachTheory(ExpressionManager exprManager) {
    Preferences.set(Preferences.OPTION_ENCODE_FIELD_ARRAY);
    encoding = new LoLLiwithQFDArrReachEncoding(exprManager);
    memoryModel = LoLLiwithQFDArrReachEncoding.createMemoryModel(encoding);
  }

  @Override
  public LoLLiwithQFDArrReachEncoding getEncoding() {
    return encoding;
  }

  @Override
  public ReachMemoryModel getMemoryModel() {
    return memoryModel;
  }
}
