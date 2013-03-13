package edu.nyu.cascade.datatypes;

import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProver;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TheoremProverFactory;
import edu.nyu.cascade.prover.TheoremProverFactory.TheoremProverFactoryException;


public class CompressedDomainNamesTest {
  private CompressedDomainNamesEncoding cdn;
  private TheoremProver theoremProver;
  private ExpressionManager exprManager;

  @Before
  public void setUp() throws ExpressionFactoryException, TheoremProverFactoryException {
    theoremProver = TheoremProverFactory.getInstance();
    exprManager = theoremProver.getExpressionManager();
    if(theoremProver instanceof edu.nyu.cascade.z3.TheoremProverImpl)
      cdn = new CompressedDomainNamesEncoding_Z3(exprManager);
    else // if (theoremProver instanceof edu.nyu.cascade.cvc4.TheoremProverImpl)
      cdn = new CompressedDomainNamesEncoding_CVC4(exprManager);
  }
  
  @Test
  public void testAssumptions() throws TheoremProverException, ExpressionFactoryException {
    theoremProver.assume( cdn.getAssumptions() );
    assertTrue( theoremProver.checkValidity(cdn.tt()).isValid() );
  }
  
  @Ignore("Too slow to Run")
  @Test
  public void testAssumptions2() throws TheoremProverException, ExpressionFactoryException {
    theoremProver.assume( cdn.getAssumptions() );
    assertTrue( !theoremProver.checkValidity(cdn.ff()).isValid() );
  }
}
