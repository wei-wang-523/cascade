package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.c.preprocessor.PreProcessor.Builder;
import edu.nyu.cascade.ir.expr.LoLLiwithQFArrReachEncoding;
import edu.nyu.cascade.ir.expr.ReachMemoryModel;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class LoLLiArrReachTheory implements Theory {
  private final LoLLiwithQFArrReachEncoding encoding;
  private final ReachMemoryModel memoryModel;
  
  public LoLLiArrReachTheory(ExpressionManager exprManager) {
    Preferences.set(Preferences.OPTION_ENCODE_FIELD_ARRAY);
    encoding = new LoLLiwithQFArrReachEncoding(exprManager);
    memoryModel = LoLLiwithQFArrReachEncoding.createMemoryModel(encoding);
  }

  @Override
  public LoLLiwithQFArrReachEncoding getEncoding() {
    return encoding;
  }

  @Override
  public ReachMemoryModel getMemoryModel() {
    return memoryModel;
  }

	@Override
  public Builder<?> getPreprocessorBuilder() {
	  // TODO Auto-generated method stub
	  return null;
  }
}
