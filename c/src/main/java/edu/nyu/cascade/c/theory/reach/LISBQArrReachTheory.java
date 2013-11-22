package edu.nyu.cascade.c.theory.reach;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.c.preprocessor.PreProcessor.Builder;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.bak.LISBQwithQFArrReachEncoding;
import edu.nyu.cascade.ir.expr.bak.ReachMemoryModel;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class LISBQArrReachTheory implements Theory {
  private final LISBQwithQFArrReachEncoding encoding;
  private final ReachMemoryModel memoryModel;
  
  public LISBQArrReachTheory(ExpressionManager exprManager) {
    Preferences.set(Preferences.OPTION_ENCODE_FIELD_ARRAY);
    encoding = new LISBQwithQFArrReachEncoding(exprManager);
    memoryModel = LISBQwithQFArrReachEncoding.createMemoryModel(encoding);
  }

  @Override
  public LISBQwithQFArrReachEncoding getEncoding() {
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

	@Override
	public CScopeAnalyzer.Builder getScopeAnalyzerBuilder() {
		// TODO Auto-generated method stub
		return null;
	}
}
