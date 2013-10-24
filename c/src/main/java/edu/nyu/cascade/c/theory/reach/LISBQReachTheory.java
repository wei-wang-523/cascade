package edu.nyu.cascade.c.theory.reach;

import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.c.preprocessor.PreProcessor.Builder;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.bak.LISBQwithQFReachEncoding;
import edu.nyu.cascade.ir.expr.bak.LISBQwithRRReachEncoding;
import edu.nyu.cascade.ir.expr.bak.ReachMemoryModel;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProver;

public class LISBQReachTheory implements Theory {
  private final ExpressionEncoding encoding;
  private final ReachMemoryModel memoryModel;
  
  public LISBQReachTheory(ExpressionManager exprManager) {
    TheoremProver tp = exprManager.getTheoremProver();
    if(tp.getProviderName().equals("cvc4")) {
      encoding = new LISBQwithRRReachEncoding(exprManager);
      memoryModel = LISBQwithRRReachEncoding.createMemoryModel(encoding);
    } else if(tp.getProviderName().equals("z3")) {
      encoding = new LISBQwithQFReachEncoding(exprManager);
      memoryModel = LISBQwithQFReachEncoding.createMemoryModel(encoding);
    } else
      throw new IllegalArgumentException("Unsupported theorem prover " + tp);
  }

  @Override
  public ExpressionEncoding getEncoding() {
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
