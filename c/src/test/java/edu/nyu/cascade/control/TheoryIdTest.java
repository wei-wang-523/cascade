package edu.nyu.cascade.control;

import static edu.nyu.cascade.c.util.TestUtils.getInjector;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import edu.nyu.cascade.datatypes.CompressedDomainNames;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProverException;

public class TheoryIdTest {
  private ExpressionManager exprManager;

  @Before
  public void setUp() {
    exprManager = getInjector().getInstance( ExpressionManager.class );
  }
  
  @Test
  public void testToTheory() throws TheoremProverException, ControlFileException {
    String qname = CompressedDomainNames.class.getName();
    TheoryId tid = new TheoryId(qname);
    Assert.assertNotNull(tid.getInstance(exprManager));
  }
}
