package edu.nyu.cascade.c;

import java.util.Map;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

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
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;

/**
 * Encodes a program path as a verification condition and checks the condition
 * for validity. Also optionally checks the path for feasibility (e.g., the path
 * (x := 0; assume x > 0; assert false) is invalid but infeasible).
 */

final class PathMergeEncoder implements PathEncoder {
  private PathEncoding pathEncoding;
  private boolean runIsValid, runIsFeasible, checkFeasibility;
  
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
  
  protected void encodeGraph(final Graph graph) throws PathFactoryException, RunProcessorException {
  	Preconditions.checkArgument(graph.isValid());
    Map<Path, Expression> pathExprMap = Maps.newHashMap();
    encodePath(graph, graph.getDestPath(), pathExprMap);
  }
  
  protected void preprocessGraph(final PreProcessor<?> preprocessor, final Graph graph) {
  	Preconditions.checkArgument(graph.isValid());
  	Set<Path> visitedPath = Sets.newHashSet();
  	preprocessPath(preprocessor, graph, graph.getDestPath(), visitedPath);
  	preprocessor.buildSnapShot();
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
    IOUtils.out().println(stmt.getLocation() + " " + stmt); 
    Expression  postCond = stmt.getPostCondition(pathEncoding, preCond);
    if(IOUtils.debugEnabled())
      IOUtils.debug().pln("Post-condition: " + postCond).flush();
    return postCond;
  }
  
  /**
   * Encode current path with a collection of pre-conditions;
   * 
	 * @return a pair of pre-condition and whether the checking 
	 * of prover is succeeded or not.
   */
  
  private Pair<Expression, Boolean> encodePathWithPreConds(Path currPath, final Iterable<Expression> preConds,
      final Iterable<Expression> preGuards) throws PathFactoryException {
    Preconditions.checkArgument(!Iterables.isEmpty(preConds));
    Preconditions.checkArgument(Iterables.size(preGuards) == Iterables.size(preConds));
    
    Expression preCond = pathEncoding.noop(preConds, preGuards); 
    return encodePathWithPreCond(currPath, preCond);
  }
  
  /**
   * Encode current path with a collection of pre-conditions
   * 
   * @return a pair of pre-condition and whether the checking 
   * of prover is succeeded or not.
   */
  private Pair<Expression, Boolean> encodePathWithPreCond(Path currPath, Expression preCond) 
  		throws PathFactoryException {
  	if(currPath.isEmpty()) return Pair.of(preCond, true);
  	
  	Expression preCondition = preCond;
  	boolean succeed = false;
    for(IRStatement stmt : currPath.getStmts()) {
    	preCondition = encodeStatement(stmt, preCondition);
      
      /* This stmt is conditional control flow graph guard */
      if(stmt.getPreLabels().contains(COND_ASSUME_LABEL))
        currPath.addGuard(preCondition.asTuple().getChild(1));
      
      succeed = checkPreCondition(preCondition, stmt);
      if(!succeed) {
        if (runIsValid() && !runIsFeasible())
          IOUtils.err().println("WARNING: path assumptions are unsatisfiable");
        return Pair.of(null, succeed);
      }
    }
    
    return Pair.of(preCondition, succeed);
  }
  
  /** 
   * Encode currPath within graph, return preCondition.
   * 
   * @return a pair of pre-condition and whether the checking 
   * of prover is succeeded or not.
   */
  private Pair<Expression, Boolean> encodePath(final Graph graph, Path currPath, Map<Path, Expression> pathExprMap) 
      throws PathFactoryException {
    if(pathExprMap.containsKey(currPath))   
    	return Pair.of(pathExprMap.get(currPath), true);
    
    Map<Path, Set<Path>> map = graph.getPredecessorMap();  
    if(map == null || !map.containsKey(currPath)) {
      Expression preCond = pathEncoding.emptyPath();
      Pair<Expression, Boolean> resPair = encodePathWithPreCond(currPath, preCond);
      if(resPair.snd()) pathExprMap.put(currPath, resPair.fst());
      return resPair;
    } else {
      Set<Path> prePaths = map.get(currPath);
      /* Collect the preconditions of pre-paths */
      ImmutableList.Builder<Expression> preCondsBuilder = new ImmutableList.Builder<Expression>();
      ImmutableList.Builder<Expression> preGuardsBuilder = new ImmutableList.Builder<Expression>();
      for(Path prePath : prePaths) {
        Pair<Expression, Boolean> resPair = encodePath(graph, prePath, pathExprMap);
        
        /* If the check is failed, stop encoding, just return */
        if(!resPair.snd())	return resPair;
        
        preCondsBuilder.add(resPair.fst());
        if(prePath.hasGuard()) {
          Expression guard = pathEncoding.getExpressionManager().and(prePath.getGuards());
          preGuardsBuilder.add(guard);
        }
      }
      
      ImmutableList<Expression> preGuards = preGuardsBuilder.build();
      ImmutableList<Expression> preConds = preCondsBuilder.build();
      
      Pair<Expression, Boolean> resPair = null;
      if(!preGuards.isEmpty()) {
        currPath.addGuard(pathEncoding.getExpressionManager().or(preGuards));
        resPair = encodePathWithPreConds(currPath, preConds, preGuards);
      } else {
      	if(preConds.size() != 1)
      		throw new PathFactoryException("Unmatched number of pre-conditions and pre-guards");
      	Expression preCond = preConds.get(0);
      	resPair = encodePathWithPreCond(currPath, preCond);
      }
      
      if(resPair.snd())	pathExprMap.put(currPath, resPair.fst());
      return resPair;
    }
  }
  
  private void preprocessPath(PreProcessor<?> preprocessor, final Graph graph, final Path path,  Set<Path> visitedPath) {
  	if(visitedPath.contains(path))	return;
  	
    if(graph.hasNullMap())	return;
    
    Map<Path, Set<Path>> map = graph.getPredecessorMap();
  	if(!map.isEmpty()) {
  		Set<Path> prePaths = map.get(path); 	
  		if(prePaths != null) {
  			for(Path prePath : prePaths) {
  				preprocessPath(preprocessor, graph, prePath, visitedPath);
  			}
  		}
  	}
  	
  	if(path.getStmts() != null) {
    	for(IRStatement stmt : path.getStmts()) {
    		preprocessor.analysis(stmt);
    	}
  	}
  	
  	visitedPath.add(path);
  }
}
