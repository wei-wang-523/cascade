package edu.nyu.cascade.c.theory.reach;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.Theory;
import edu.nyu.cascade.c.preprocessor.PreProcessor.Builder;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.ir.expr.bak.LoLLiwithQFReachEncoding;
import edu.nyu.cascade.ir.expr.bak.LoLLiwithRRReachEncoding;
import edu.nyu.cascade.ir.expr.bak.ReachEncoding;
import edu.nyu.cascade.ir.expr.bak.ReachMemoryModel;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProver;

public class LoLLiReachTheory implements Theory {
  private final ReachEncoding encoding;
  private final ReachMemoryModel memoryModel;
  
  public LoLLiReachTheory(ExpressionManager exprManager) {
    TheoremProver tp = exprManager.getTheoremProver();
    if(tp.getProviderName().equals("cvc4")) {
      encoding = new LoLLiwithRRReachEncoding(exprManager);
      memoryModel = LoLLiwithRRReachEncoding.createMemoryModel(encoding);
    } else if(tp.getProviderName().equals("z3")) {
      encoding = new LoLLiwithQFReachEncoding(exprManager);
      memoryModel = LoLLiwithQFReachEncoding.createMemoryModel(encoding);
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

	@Override
	public CScopeAnalyzer.Builder getScopeAnalyzerBuilder() {
		// TODO Auto-generated method stub
		return null;
	}
}
