package edu.nyu.cascade.c;

import java.util.List;

import com.google.common.base.Stopwatch;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.expr.PathFactoryException;
import edu.nyu.cascade.ir.path.PathEncoding;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateExpressionClosure;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;

/**
 * Encodes a program path as a verification condition and checks the condition
 * for validity. Also optionally checks the path for feasibility (e.g., the path
 * (x := 0; assume x > 0; assert false) is invalid but infeasible).
 */
final class PathSeqEncoder implements PathEncoder<List<IRStatement>> {
  private PathEncoding pathEncoding;  // the encoding to use for the path
  private StateExpression path;  // the expression representing the encoded path 
  private boolean runIsValid, runIsFeasible, checkFeasibility;
  private final Stopwatch timer = Stopwatch.createUnstarted();
  
  PathSeqEncoder(PathEncoding pathEncoding) {
    this.pathEncoding = pathEncoding;
    checkFeasibility = false;
    reset();
  }

  static PathSeqEncoder create(PathEncoding encoding) {
    return new PathSeqEncoder(encoding);
  }
  
  @Override
  public void reset() {
    path = pathEncoding.emptyState();
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
  
  @Override
  public boolean runIsReachable() {
  	throw new UnsupportedOperationException();
  }
  

  @Override
  public void encode(PreProcessor<?> preprocessor, List<IRStatement> path)
      throws PathFactoryException {
  	if(preprocessor != null) {
  		timer.start();
      for(IRStatement stmt : path) preprocessor.analysis(stmt);
	    IOUtils.stats().pln("Preprocessing took time: " + timer.stop());
	    CScopeAnalyzer.reset();
  	}
  	
  	for (IRStatement stmt : path) {
  		IOUtils.out().println(stmt.getLocation() + " " + stmt); 
  		if (!encodeStatement(stmt))
  			break;
  	}
  	
  	CScopeAnalyzer.reset();
  }

  @Override
  public void checkReach(PreProcessor<?> preprocessor, List<IRStatement> path,
      String label) throws PathFactoryException {
  	throw new UnsupportedOperationException();
  }

  @Override
	public void checkReachIncremental(PreProcessor<?> preprocessor, List<IRStatement> graph, 
			String label) throws PathFactoryException {
  	throw new UnsupportedOperationException();
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
    
    StateExpressionClosure pre = stmt
    		.getPreCondition(pathEncoding.getExpressionEncoder());
    
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
              IOUtils.out().println("\nCounter-example:\n" + result.getCounterExampleToString());
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
