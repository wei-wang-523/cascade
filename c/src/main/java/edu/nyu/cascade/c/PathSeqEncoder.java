package edu.nyu.cascade.c;

import java.util.List;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.expr.ExpressionClosure;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.PathEncoding;
import edu.nyu.cascade.ir.expr.PathFactoryException;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;

/**
 * Encodes a program path as a verification condition and checks the condition
 * for validity. Also optionally checks the path for feasibility (e.g., the path
 * (x := 0; assume x > 0; assert false) is invalid but infeasible).
 */
final class PathSeqEncoder implements PathEncoder {
  private PathEncoding pathEncoding;  // the encoding to use for the path
  private Expression path;  // the expression representing the encoded path 
  private boolean runIsValid, runIsFeasible, checkFeasibility;

  PathSeqEncoder(PathEncoding pathEncoding) {
    this.pathEncoding = pathEncoding;
    checkFeasibility = false;
    reset();
  }

  static PathSeqEncoder create(PathEncoding encoding) {
    return new PathSeqEncoder(encoding);
  }

  @Override
  public ExpressionEncoder getExpressionEncoder() {
    return pathEncoding.getExpressionEncoder();
  }
  
  @Override
  public void reset() {
    path = pathEncoding.emptyPath();
    runIsValid = true;
    runIsFeasible = true;
  }
  
  @Override
  public boolean runIsFeasible() throws PathFactoryException {
    return runIsFeasible;
  }

  @Override
  public boolean runIsValid() {
    return runIsValid;
  }
  
  @Override
  public void setFeasibilityChecking(boolean b) {
    checkFeasibility = b;
  }

  protected void preprocessPath(PreProcessor<?> preprocessor, List<IRStatement> path) {
    for(IRStatement stmt : path) {
    	preprocessor.analysis(stmt);
    }
    pathEncoding.getExpressionEncoder()
    	.getMemoryModel().setPreProcessor(preprocessor);
  }
  
  protected void encodePath(List<IRStatement> path) throws PathFactoryException {
  	for (IRStatement stmt : path) {
  		IOUtils.out().println(stmt.getLocation() + " " + stmt); 
  		if (!encodeStatement(stmt))
  			break;
  	}
  }

/**
   * Encode the given statement as an extension of the current path.
   * 
   * @param stmt
   *          the statement to encode
   * @return false if the statement results in an invalid verification condition
   *         or an infeasible path; true otherwise.
   */
  private boolean encodeStatement(IRStatement stmt) throws PathFactoryException {
    
    /* Precondition is OK, encode the postcondition. */
    path = stmt.getPostCondition(pathEncoding, path);
    
    if(IOUtils.debugEnabled())
      IOUtils.debug().pln("Post-condition: " + path).flush();
    
    ExpressionClosure pre = stmt.getPreCondition(pathEncoding.getExpressionEncoder());
    
    if (pre != null) {
      /* If the statement has a precondition, we have to check it before continuing with 
       * the encoding.
       */
      IOUtils.debug().pln("Checking pre-condition: " + pre).flush();
      ValidityResult<?> result = pathEncoding.checkAssertion(path, pre);

      IOUtils.debug().pln("Result: " + result).flush();
      runIsValid = result.isValid();
      
      if (!runIsValid) {
        if ( result.isInvalid() ) {
          if( Preferences.isSet(Preferences.OPTION_COUNTER_EXAMPLE) )
            if(result.getCounterExample().isEmpty())
              IOUtils.out().println("\nCounter-example:\n" + result.getUnknown_reason());
            else
              IOUtils.out().println("\nCounter-example:\n" + result.getCounterExample());
        } else { // result.isUnknown()
          IOUtils.out().println("Unkown: " + result.getUnknown_reason());
        }
        return false;
      } else if (checkFeasibility) {
        IOUtils.out().println("Checking path feasibility.");
        SatResult<?> res = pathEncoding.checkPath(path);
        IOUtils.out().println("Result: " + res);
        runIsFeasible = !res.isUnsatisfiable();
      }
    }
    
    return true;
  }
}
