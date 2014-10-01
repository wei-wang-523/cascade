package edu.nyu.cascade.datatypes;

import com.google.inject.Inject;

import edu.nyu.cascade.c.theory.Theory;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Preferences;

public class CompressedDomainNames implements Theory {
  private final CompressedDomainNamesEncoding encoding;
  
  @Inject
  public CompressedDomainNames(ExpressionManager exprManager) {
    String tpProviderName = exprManager.getTheoremProver().getProviderName();
    if(Preferences.PROVER_Z3.equals(tpProviderName))
      encoding = CompressedDomainNamesEncoding_Z3.create(exprManager);
    else if (Preferences.PROVER_CVC4.equals(tpProviderName))
      encoding = CompressedDomainNamesEncoding_CVC4.create(exprManager);
    else
      throw new IllegalArgumentException("Unknown theorem prover " + tpProviderName);
  }

	@Override
  public ExpressionEncoding getEncoding() {
	  return encoding;
  }
  
  
}
