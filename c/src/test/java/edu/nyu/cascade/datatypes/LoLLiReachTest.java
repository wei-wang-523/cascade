package edu.nyu.cascade.datatypes;

import static org.junit.Assert.assertTrue;

//import java.io.FileNotFoundException;
//import java.io.PrintStream;
//import edu.nyu.cascade.util.IOUtils;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import edu.nyu.cascade.ir.expr.LoLLiReachEncoding;
import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.ir.expr.LoLLiwithQFReachEncoding;
import edu.nyu.cascade.ir.expr.LoLLiwithRRReachEncoding;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProver;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TheoremProverFactory;
import edu.nyu.cascade.prover.TheoremProverFactory.TheoremProverFactoryException;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public class LoLLiReachTest {
  private LoLLiReachEncoding encoding;
  private TheoremProver theoremProver;
  private ExpressionManager exprManager;

  @Before
  public void setUp() throws ExpressionFactoryException, TheoremProverFactoryException {
//    try {
//      String path = "/Users/Wei/Workspace/tmp/test.smt2";
//      IOUtils.enableTpFile();
//      IOUtils.setTpFileStream(new PrintStream(path));
      theoremProver = TheoremProverFactory.getInstance();
      exprManager = theoremProver.getExpressionManager();
      String tpProviderName = theoremProver.getProviderName();
      if("cvc4".equals(tpProviderName))
        encoding = new LoLLiwithRRReachEncoding(exprManager);
      else if ("z3".equals(tpProviderName))
        encoding = new LoLLiwithQFReachEncoding(exprManager);
      else
        throw new IllegalArgumentException("Unsupported theorem prover " + theoremProver);
//    } catch (FileNotFoundException e) {
//      e.printStackTrace();
//    }
  }
  
  @Test
  public void testAssumptions() throws TheoremProverException, ExpressionFactoryException {
    theoremProver.assume( encoding.getAssumptions() );
    assertTrue( theoremProver.checkValidity(encoding.tt()).isValid() );
  }
  
  @Ignore
  @Test
  public void testAssumptions2() throws TheoremProverException, ExpressionFactoryException {
    theoremProver.assume( encoding.getAssumptions() );
    assertTrue( !theoremProver.checkValidity(encoding.ff()).isValid() );
  }
  
  /** Example0 */
  @Ignore
  @Test
  public void testAssumptions3() throws TheoremProverException, ExpressionFactoryException {
    theoremProver.assume( encoding.getAssumptions() );
    Type eltType = encoding.getEltType();
    VariableExpression e1 = exprManager.variable("e1", eltType, false);
    VariableExpression e2 = exprManager.variable("e2", eltType, false);
    VariableExpression e3 = exprManager.variable("e3", eltType, false);
    BooleanExpression targetExpr = exprManager.not(
        exprManager.implies(
            exprManager.and(
                exprManager.not(e1.eq(e2)), 
                applyRfAvoid(e1, e2, e3),
                applyRfAvoid(e2, e3, e3)), // applyRf(e1, e2, e3)
            exprManager.and(
                applyRfAvoid(e1, applyF(e1), e3), 
                applyRfAvoid(applyF(e1), e3, e3))) // applyRf(e1, applyF(e1), e3))
        );
    assertTrue( theoremProver.checkSat(targetExpr).isUnsatisfiable());
  }
  
  /** Thomas' example1 */
  @Ignore
  @Test
  public void testAssumptions4() throws TheoremProverException, ExpressionFactoryException {
    theoremProver.assume( encoding.getAssumptions() );
    Type eltType = encoding.getEltType();
    VariableExpression e1 = exprManager.variable("e1", eltType, false);
    VariableExpression e2 = exprManager.variable("e2", eltType, false);
    VariableExpression e3 = exprManager.variable("e3", eltType, false);
    VariableExpression e4 = exprManager.variable("e4", eltType, false);
    BooleanExpression targetExpr = exprManager.not(
        exprManager.implies(
            exprManager.and(
                applyRfAvoid(e1, e2, e3), //applyRf(e1, e2, e3)
                applyRfAvoid(e2, e3, e3),
                exprManager.not(e2.eq(e3)),
                e4.eq(applyF(e2))),
            exprManager.and(
                applyRfAvoid(e1, e4, e3),
                applyRfAvoid(e4, e3, e3))) //applyRf(e1, e4, e3)
        );
    assertTrue( theoremProver.checkSat(targetExpr).isUnsatisfiable());
  }
  
  /** Thomas' example2 
   * FIXME: LoLLiwithRR and LoLLiwithQF has inconsistent result
   */
  @Ignore
  @Test
  public void testAssumptions5() throws TheoremProverException, ExpressionFactoryException {
    theoremProver.assume( encoding.getAssumptions() );
    Type eltType = encoding.getEltType();
    Expression nil = encoding.getNil();
    VariableExpression e1 = exprManager.variable("e1", eltType, false);
    VariableExpression e2 = exprManager.variable("e2", eltType, false);
    BooleanExpression targetExpr = exprManager.not(
        exprManager.implies(
            exprManager.and(
                applyRfAvoid(e1, nil, nil),
                applyJoin(e1, e2).eq(nil)
                ),
            exprManager.or(
                exprManager.and(
                    applyRfAvoid(e1, nil, e2),
                    applyRfAvoid(e1, nil, nil),
                    applyRfAvoid(e1, e2, nil),
                    e2.neq(nil)
                    ),                  
                exprManager.and(
                    applyRfAvoid(e1, nil, e2),
                    applyRfAvoid(e1, nil, e2), // applyRf(e1, nil, e2)
                    applyRfAvoid(nil, e2, e2),
                    applyRfAvoid(e1, e2, nil),
                    e2.neq(nil)
                    ),
                exprManager.and(
                    applyRfAvoid(e1, nil, nil),
                    applyRfAvoid(e1, nil, e2)
                    )
                )
            )
        );
    assertTrue( theoremProver.checkSat(targetExpr).isUnsatisfiable());
  }
  
  /** Thomas' example3 */
  @Test
  public void testAssumptions6() throws TheoremProverException, ExpressionFactoryException {
    theoremProver.assume( encoding.getAssumptions() );
    Type eltType = encoding.getEltType();
    Expression nil = encoding.getNil();
    VariableExpression e1 = exprManager.variable("e1", eltType, false);
    VariableExpression e2 = exprManager.variable("e2", eltType, false);
    BooleanExpression targetExpr = exprManager.not(
        exprManager.implies(
            exprManager.and(
                applyRfAvoid(e2, nil, nil),
                e2.neq(nil)
                ),
            exprManager.or(
                exprManager.and(
                    exprManager.not(applyRfAvoid(applyF(e2), e2, e2)),
                    exprManager.not(applyRfAvoid(e1, e2, e2))
                    ),                  
                exprManager.and(
                    applyRfAvoid(e1, e2, e2),
                    exprManager.not(applyRfAvoid(applyF(e2), e1, e1))
                    )
                )
            )
        );
    assertTrue( theoremProver.checkSat(targetExpr).isUnsatisfiable());
  }
  
  /** Thomas' example 4 
   * FIXME: LoLLiwithRR and LoLLiwithQF has inconsistent result
   */
  @Test
  public void testAssumptions7() throws TheoremProverException, ExpressionFactoryException {
    theoremProver.assume( encoding.getAssumptions() );
    Type eltType = encoding.getEltType();
    Expression nil = encoding.getNil();
    VariableExpression e1 = exprManager.variable("e1", eltType, false);
    VariableExpression e2 = exprManager.variable("e2", eltType, false);
    BooleanExpression targetExpr = exprManager.not(
        exprManager.implies(
            exprManager.and(
                applyJoin(e1, e2).eq(nil),
                applyRfAvoid(e2, nil, nil),
                e2.neq(nil)
                ),
            exprManager.not(applyRfAvoid(e2, e2, e2)) //applyRf(e2, e2, e2)
            )
        );
    assertTrue( theoremProver.checkSat(targetExpr).isUnsatisfiable());
  }
  
  /** Example5 */
  @Test
  public void testAssumptions8() throws TheoremProverException, ExpressionFactoryException {
    theoremProver.assume( encoding.getAssumptions() );
    Type eltType = encoding.getEltType();
    VariableExpression e1 = exprManager.variable("e1", eltType, false);
    VariableExpression e2 = exprManager.variable("e2", eltType, false);
    BooleanExpression targetExpr = exprManager.and(
        applyF(applyF(e1)).eq(e1),
        applyRfAvoid(e1, e2, e2),
        e1.neq(e1),
        e2.neq(applyF(e1))
        );
    assertTrue( theoremProver.checkSat(targetExpr).isUnsatisfiable());
  }
  
  private Expression applyRfAvoid(Expression ... args) {
    return encoding.functionCall("rf_avoid", args);
  }
  
  private Expression applyF(Expression arg) {
    return encoding.functionCall("f", arg);
  }
  
  private Expression applyJoin(Expression ... args) {
    return encoding.functionCall("join", args);
  }
}
