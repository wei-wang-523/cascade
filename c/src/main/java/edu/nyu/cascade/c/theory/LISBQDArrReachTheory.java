package edu.nyu.cascade.c.theory;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.c.preprocessor.PreProcessor.Builder;
import edu.nyu.cascade.ir.expr.LISBQwithQFDArrReachEncoding;
import edu.nyu.cascade.ir.expr.ReachMemoryModel;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class LISBQDArrReachTheory implements Theory {
  private final LISBQwithQFDArrReachEncoding encoding;
  private final ReachMemoryModel memoryModel;
  
  public LISBQDArrReachTheory(ExpressionManager exprManager) {
    Preferences.set(Preferences.OPTION_ENCODE_FIELD_ARRAY);
    encoding = new LISBQwithQFDArrReachEncoding(exprManager);
    memoryModel = LISBQwithQFDArrReachEncoding.createMemoryModel(encoding);
  }

  @Override
  public LISBQwithQFDArrReachEncoding getEncoding() {
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
