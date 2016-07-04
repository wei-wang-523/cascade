package edu.nyu.cascade.theory;

import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import edu.nyu.cascade.datatypes.CompressedDomainNames;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProver;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TheoremProverFactory;
import edu.nyu.cascade.prover.TheoremProverFactory.TheoremProverFactoryException;

public class CompressedDomainNamesTest {
	private ExpressionEncoding cdn;
	private TheoremProver theoremProver;
	private ExpressionManager exprManager;

	@Before
	public void setUp() throws ExpressionFactoryException,
	    TheoremProverFactoryException {
		theoremProver = TheoremProverFactory.getInstance();
		exprManager = theoremProver.getExpressionManager();
		cdn = new CompressedDomainNames(exprManager).getEncoding();
	}

	@Ignore("Bug with z3 push scope")
	@Test
	public void testAssumptions() throws TheoremProverException,
	    ExpressionFactoryException {
		theoremProver.assume(cdn.getAssumptions());
		assertTrue(theoremProver.checkValidity(cdn.tt()).isValid());
	}

	@Ignore("Too slow to Run")
	@Test
	public void testAssumptions2() throws TheoremProverException,
	    ExpressionFactoryException {
		theoremProver.assume(cdn.getAssumptions());
		assertTrue(!theoremProver.checkValidity(cdn.ff()).isValid());
	}
}
