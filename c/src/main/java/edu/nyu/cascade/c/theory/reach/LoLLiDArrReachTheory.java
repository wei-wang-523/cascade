package edu.nyu.cascade.c.theory.reach;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.c.preprocessor.PreProcessor.Builder;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.bak.LoLLiwithQFDArrReachEncoding;
import edu.nyu.cascade.ir.expr.bak.ReachMemoryModel;
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
  public MemoryModel getMemoryModel() {
    return (MemoryModel) memoryModel;
  }

	@Override
  public Builder<?> getPreprocessorBuilder() {
	  // TODO Auto-generated method stub
	  return null;
  }
}
