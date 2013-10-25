package edu.nyu.cascade.c;

import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

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

final class PathMergeEncoder implements PathEncoder {
  private PathEncoding pathEncoding;
  private boolean runIsValid, runIsFeasible, checkFeasibility;
  private boolean succeed;
  
  PathMergeEncoder(PathEncoding pathEncoding) {
    this.pathEncoding = pathEncoding;
    checkFeasibility = false;
    reset();
  }

  static PathMergeEncoder create(PathEncoding encoding) {
    return new PathMergeEncoder(encoding);
  }

  @Override
  public ExpressionEncoder getExpressionEncoder() {
    return pathEncoding.getExpressionEncoder();
  }
  
  @Override
  public void reset() {
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
  
  protected Expression encodeGraph(final Graph graph) throws PathFactoryException {
    Map<Path, Expression> pathExprMap = Maps.newHashMap();
    return encodePath(graph, graph.destPath, pathExprMap);
  }
  
  protected void preprocessGraph(final PreProcessor<?> preprocessor, final Graph graph) {
  	preprocessPath(preprocessor, graph.predecessorMap, graph.destPath);
  	pathEncoding.getExpressionEncoder()
  		.getMemoryModel().setPreProcessor(preprocessor);
  }

  /**
   * Check the current statement's pre-condition 
   * 
   * @param stmt
   *          the statement to encode
   * @return false if the statement results in an invalid verification condition
   *         or an infeasible path; true otherwise.
   */
  private boolean checkPreCondition(Expression preCond, IRStatement stmt) 
      throws PathFactoryException {    

    ExpressionClosure pre = stmt.getPreCondition(pathEncoding.getExpressionEncoder());
    if (pre != null) {
      /* If the statement has a precondition, we have to check it before continuing with 
       * the encoding.
       */
      IOUtils.debug().pln("Checking pre-condition: " + pre).flush();
      ValidityResult<?> result = pathEncoding.checkAssertion(preCond, pre);

      IOUtils.out().println("Result: " + result);
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
        SatResult<?> res = pathEncoding.checkPath(preCond);
        IOUtils.out().println("Result: " + res);
        runIsFeasible = !res.isUnsatisfiable();
        return runIsFeasible;
      }
    }   
    return true;
  }
 
  /** Encode statement stmt, with single pre-condition */
  private Expression encodeStatement(IRStatement stmt, final Expression preCond) 
      throws PathFactoryException {
    /* Precondition is OK, encode the postcondition. */
    IOUtils.err().println(stmt.getLocation() + " " + stmt); 
    Expression  postCond = stmt.getPostCondition(pathEncoding, preCond);
    if(IOUtils.debugEnabled())
      IOUtils.debug().pln("Post-condition: " + postCond).flush();
    return postCond;
  }
  
  /**
   * Encode current path with a collection of pre-conditions;
   * return null, if encoding of one pre-path failed
   */
  private Expression encodePathWithPreConds(Path currPath, final Iterable<Expression> preConds,
      final Iterable<Expression> preGuards) throws PathFactoryException {
    Preconditions.checkArgument(preConds != null && !Iterables.isEmpty(preConds));
    Preconditions.checkArgument(preGuards == null ||
        Iterables.size(preGuards) == Iterables.size(preConds));
    
    Expression preCond = null;
    
    int size = Iterables.size(preConds);
    if(size == 1) {
      preCond = Iterables.get(preConds, 0);
    } else {
      /* more than one preConds and preGuards, merge it before encode statement */
      preCond = pathEncoding.noop(preConds, preGuards);      
    }

    for(IRStatement stmt : currPath.stmts) {
      preCond = encodeStatement(stmt, preCond);
      
      /* This stmt is conditional control flow graph guard */
      if(stmt.getPreLabels().contains(COND_ASSUME_LABEL))
        currPath.addGuard(preCond.asTuple().getChild(1));
      
      succeed = checkPreCondition(preCond, stmt);
      if(!succeed) {
        if (runIsValid() && !runIsFeasible())
          IOUtils.err().println("WARNING: path assumptions are unsatisfiable");
        return null;
      }
    }
    
    return preCond;
  }
  
  /** 
   * Encode currPath within graph, return preCondition; 
   * return null, if encoding of one pre-path failed
   */
  private Expression encodePath(final Graph graph, Path currPath, Map<Path, Expression> pathExprMap) 
      throws PathFactoryException {
    if(pathExprMap.containsKey(currPath))   
      return pathExprMap.get(currPath);
    
    List<Expression> preConds = null, preGuards = null;
    Map<Path, Set<Path>> map = graph.predecessorMap;  
    if(map == null)
      preConds = Lists.newArrayList(pathEncoding.emptyPath());
    else {    
      Set<Path> prePaths = graph.predecessorMap.get(currPath);
      if(prePaths == null) {
        preConds = Lists.newArrayList(pathEncoding.emptyPath());
      } else {
        /* Collect the preconditions of pre-paths */
        preConds = Lists.newArrayList();
        for(Path prePath : prePaths) {
          Expression preCond = encodePath(graph, prePath, pathExprMap);
          if(preCond == null)  return null;
          preConds.add(preCond);
          if(prePath.hasGuard()) {
            Expression guard = pathEncoding.getExpressionManager().and(prePath.guards);
            if(preGuards == null) 
              preGuards = Lists.newArrayList(guard);
            else
              preGuards.add(guard);
          }
        }
        if(preGuards != null && !preGuards.isEmpty()) {
          currPath.addGuard(pathEncoding.getExpressionManager().or(preGuards));
        }
      }
    }
    Expression pathExpr = encodePathWithPreConds(currPath, preConds, preGuards);
    pathExprMap.put(currPath, pathExpr);
    return pathExpr;
  }
  
  private void preprocessPath(PreProcessor<?> preprocessor, final Map<Path, Set<Path>> map, final Path path) {
  	Preconditions.checkArgument(map != null);
  	if(!map.isEmpty()) {
  		Set<Path> prePaths = map.get(path); 	
  		if(prePaths != null) {
  			for(Path prePath : prePaths) {
  				preprocessPath(preprocessor, map, prePath);
  			}
  		}
  	}
  	
  	if(path.stmts != null) {
    	for(IRStatement stmt : path.stmts) {
    		preprocessor.analysis(stmt);
    	}
  	}
  }
}
