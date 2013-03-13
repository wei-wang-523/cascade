package edu.nyu.cascade.datatypes;

import static org.junit.Assert.assertTrue;

//import java.io.FileNotFoundException;
//import java.io.PrintStream;
//import edu.nyu.cascade.util.IOUtils;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import edu.nyu.cascade.ir.expr.ExpressionFactoryException;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.TheoremProver;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.TheoremProverFactory;
import edu.nyu.cascade.prover.TheoremProverFactory.TheoremProverFactoryException;

public class LengthTest {
  private ListEncoding listEncoding;
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
      
      if(theoremProver instanceof edu.nyu.cascade.cvc4.TheoremProverImpl)
        listEncoding = new ListEncoding_CVC4(exprManager);
      else if(theoremProver instanceof edu.nyu.cascade.z3.TheoremProverImpl)
        listEncoding = new ListEncoding_Z3(exprManager);
      else
        throw new IllegalArgumentException("Unsupported theorem prover " + theoremProver);
//    } catch (FileNotFoundException e) {
//      e.printStackTrace();
//    }
  }
  
  @Test
  public void testAssumptions() throws TheoremProverException, ExpressionFactoryException {
    theoremProver.assume( listEncoding.getAssumptions() );
    assertTrue( theoremProver.checkValidity(listEncoding.tt()).isValid() );
  }
  
  @Test
  @Ignore
  public void testAssumptions2() throws TheoremProverException, ExpressionFactoryException {
    theoremProver.assume( listEncoding.getAssumptions() );
    assertTrue( !theoremProver.checkValidity(listEncoding.ff()).isValid() );
  }
  
  @Test
  public void testAssumptions3() throws TheoremProverException, ExpressionFactoryException {
    theoremProver.assume( listEncoding.getAssumptions() );
    ExpressionManager exprManager = listEncoding.getExpressionManager();
    Expression listNil = listEncoding.applyNilConstr();
    Expression list1 = listEncoding.applyConsConstr(exprManager.constant(3), listNil);
    Expression list2 = listEncoding.applyConsConstr(exprManager.constant(2), list1);
    Expression list3 = listEncoding.applyConsConstr(exprManager.constant(1), list2);
    IntegerExpression lengthExpr = listEncoding.applyLengthList(list3);
    BooleanExpression targetExpr = lengthExpr.neq(exprManager.constant(3));
    assertTrue( theoremProver.checkSat(targetExpr).isUnsatisfiable());
  }
}
