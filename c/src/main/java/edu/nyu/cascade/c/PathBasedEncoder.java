package edu.nyu.cascade.c;

import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.List;
import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.base.Stopwatch;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Queues;
import com.google.common.collect.Table;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.PathFactoryException;
import edu.nyu.cascade.ir.path.PathEncoding;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateExpressionClosure;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.Triple;

/**
 * Encodes a program path as a verification condition and checks the condition
 * for validity. Also optionally checks the path for feasibility (e.g., the path
 * (x := 0; assume x > 0; assert false) is invalid but infeasible).
 * 
 * It is a path-unit encoder, first encoding each path separately as path state
 * closure , then combines then based on graph structure
 * 
 * @author wei
 */

class PathBasedEncoder implements PathEncoder<PathGraph> {
  private final PathEncoding pathEncoding;
  private final PathStateFactory pathStateFactory;
  private boolean runIsValid, runIsFeasible, runIsReachable, checkFeasibility;
  private Multimap<Path, Path> loopExitMap ,loopEnterMap, loopInitMap, loopBackMap;
  private final Stopwatch timer = Stopwatch.createUnstarted();
  
  PathBasedEncoder(PathEncoding pathEncoding) {
    this.pathEncoding = pathEncoding;
    
    pathStateFactory = PathStateFactory.getInstance(pathEncoding);
    checkFeasibility = false;
    reset();
  }

  static PathBasedEncoder create(PathEncoding encoding) {
    return new PathBasedEncoder(encoding);
  }

  @Override
  public void reset() {
    runIsValid = true;
    runIsFeasible = true;
    runIsReachable = false;
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
  public boolean runIsReachable() {
  	return runIsReachable;
  }
  
  @Override
  public void setFeasibilityChecking(boolean b) {
    checkFeasibility = b;
  }

  @Override
	public void encode(PreProcessor<?> preprocessor, PathGraph graph) 
			throws PathFactoryException {
		Preconditions.checkArgument(graph.isValid());
		
		/* label the exit paths and entry paths for every loop entry */
		List<Multimap<Path, Path>> loopRoadMap = PathGraph.getLoopInfo(graph);
		loopInitMap = loopRoadMap.get(0);
		loopEnterMap = loopRoadMap.get(1);
	  loopBackMap = loopRoadMap.get(2);
		loopExitMap = loopRoadMap.get(3);
		
		/* Initialize the iteration times map */
		ImmutableMap<Path, Integer> iterTimesMap = PathGraph.initIterTimesMap(graph);
	  
		if(preprocessor != null) {
			timer.start();
			preprocessDFS(preprocessor, graph, iterTimesMap);
	    IOUtils.stats().pln("Preprocessing took time: " + timer.stop());
	    CScopeAnalyzer.reset();
		}
		
		timer.start();
		statePropagateDFS(graph, iterTimesMap);
  	IOUtils.stats().pln("Encoding took time " + timer.stop());
  	
		CScopeAnalyzer.reset();
	}
	
  @Override
	public void checkReach(PreProcessor<?> preprocessor, PathGraph graph, String label) 
			throws PathFactoryException {
		Preconditions.checkArgument(graph.isValid());
		
		/* label the exit paths and entry paths for every loop entry */
		List<Multimap<Path, Path>> loopRoadMap = PathGraph.getLoopInfo(graph);
		loopInitMap = loopRoadMap.get(0);
		loopEnterMap = loopRoadMap.get(1);
	  loopBackMap = loopRoadMap.get(2);
		loopExitMap = loopRoadMap.get(3);
		
		/* Initialize the iteration times map */
		ImmutableMap<Path, Integer> iterTimesMap = PathGraph.initIterTimesMap(graph);
	  
		if(preprocessor != null) {
			timer.start();
			preprocessDFS(preprocessor, graph, iterTimesMap);
	    IOUtils.stats().pln("Preprocessing took time: " + timer.stop());
	    CScopeAnalyzer.reset();
		}
		
		timer.start();
		checkReachDFS(graph, label, iterTimesMap);
  	IOUtils.stats().pln("Encoding took time " + timer.stop());
		CScopeAnalyzer.reset();
	}
	
	@Override
	public void checkReachIncremental(PreProcessor<?> preprocessor, 
			PathGraph graph, 
			String label) throws PathFactoryException {
		Preferences.isSet(Preferences.OPTION_ITERATION_TIMES);
		Preferences.isSet(Preferences.OPTION_INCREMENTAL);
				
		/* label the exit paths and entry paths for every loop entry */
		List<Multimap<Path, Path>> loopRoadMap = PathGraph.getLoopInfo(graph);
		loopInitMap = loopRoadMap.get(0);
		loopEnterMap = loopRoadMap.get(1);
	  loopBackMap = loopRoadMap.get(2);
		loopExitMap = loopRoadMap.get(3);
		
		CScopeAnalyzer.reset();
		
		/* Initialize the iteration times map */
		ImmutableMap<Path, Integer> iterTimesMap = PathGraph.initIterTimesMap(graph);
		
	 	/* Pre-processing for mode Partition and Burstall */
		if(preprocessor != null) {
			timer.start();
			preprocessDFS(preprocessor, graph, iterTimesMap);
	    IOUtils.stats().pln("Preprocessing took time: " + timer.stop());
	    CScopeAnalyzer.reset();
		}
		
		timer.start();
		checkReachDFSLoopMerge(graph, label, iterTimesMap);
  	IOUtils.stats().pln("Encoding took time " + timer.stop());
		CScopeAnalyzer.reset();
	}
	
  /**
   * Propagate state expression to successor paths via BFS, <code>pathStateClosureMap
   * </code> is passed around state propagate and state propagate in the function
   * call, cause different function calls may visited the same paths (called the same
   * functions).
   * 
   * @param graph
   * @return
   * @throws PathFactoryException 
   */
  private void checkReachDFS(PathGraph graph, 
  		String label, 
  		ImmutableMap<Path, Integer> iterTimesMap) 
  				throws PathFactoryException {
  	
  	IOUtils.out().println("\nAnalyzing ...");
  	
  	Map<Path, Integer> currIterTimesMap = Maps.newHashMap(iterTimesMap);
  	Map<Path, PathStateClosure> cleanPathStateClosureMap = Maps.newHashMap();
    Table<Path, Path, PathStateClosure> phiNodeTable = HashBasedTable.create();
  	
  	Deque<Path> queue = Queues.newArrayDeque();  	
  	queue.push(graph.getSrcPath());
  	
  	while(!queue.isEmpty()) {
  		Path path = queue.pop();
  		
			IOUtils.out().println(path.stmtsToString());
			
			/* Encode the path as path state closure whenever need it */
			PathStateClosure cleanPathStateClosure;
			
			if(!cleanPathStateClosureMap.containsKey(path)) {
				cleanPathStateClosure = getPathStateClosure(path);
				cleanPathStateClosureMap.put(path, cleanPathStateClosure);
			} else {
				cleanPathStateClosure = cleanPathStateClosureMap.get(path); 
			}
			
			/* Get the path state of current path */
			PathStateClosure currPathStateClosure;
			
			if(path == graph.getSrcPath()) {
				currPathStateClosure = cleanPathStateClosure;
			} else {
				
				Map<Path, PathStateClosure> phiNode = phiNodeTable.row(path);
				PathStateClosure preMergeStateClosure = pathStateFactory.
						mergePreStateClosure( phiNode.values());
				
				/* clean phi node for further collection */
				phiNode.clear();
				
				/* substitute state variable of current path */
				currPathStateClosure = cleanPathStateClosure.apply(preMergeStateClosure);
			}
  		
			if(path.isFuncEnt()) {
				Triple<Path, PathStateClosure, Boolean> resFuncTriple = checkReachFuncDFS(
						graph, label, path, currPathStateClosure, currIterTimesMap, cleanPathStateClosureMap);
				if(!resFuncTriple.thd()) return;
				
				path = resFuncTriple.fst();
				currPathStateClosure = resFuncTriple.snd();
			}
  		
			if(path.hasLabel(label))	{
				IOUtils.out().println("Checking path reachability.");
				StateExpression state = currPathStateClosure.getPathState();
        SatResult<?> res = pathEncoding.checkPath(state);
        IOUtils.out().println("Result: " + res);
        runIsReachable = res.isSatisfiable();
        if(!runIsReachable)	return;
        
        if( Preferences.isSet(Preferences.OPTION_COUNTER_EXAMPLE) )
        	IOUtils.out().println("\nCounter-example:\n" + res.getUnknown_reason());
			}
			
      /* find all the successors of path */
			Collection<Path> successors = getSuccessorsViaUnroll(graph, path, currIterTimesMap);

			/* propagate to all successors' phi-node */
			for(Path succ : successors) {
				phiNodeTable.put(succ, path, currPathStateClosure);
				
				/* Process the path until all its predecessors are encoded */
				int completeSize = getCompleteSize(graph, succ, currIterTimesMap);
				Map<Path, PathStateClosure> succPhiNode = phiNodeTable.row(succ);	
				if(succPhiNode.size() == completeSize) queue.push(succ);
			}
  	}
  }
  
  /**
   * Propagate path state closure of function ent path <code>entPath</code>
   * to its successors until reach the the function ret path
   * 
   * @param graph
   * @param label
   * @param entPath
   * @param entStateClosure 
   * @param currIterTimesMap
   * @param cleanPathStateClosureMap
   * @return
   * @throws PathFactoryException
   */
  private Triple<Path, PathStateClosure, Boolean> checkReachFuncDFS(
  		PathGraph graph, 
  		String label,
  		Path entPath,
  		PathStateClosure entStateClosure, 
  		Map<Path, Integer> currIterTimesMap,
  		Map<Path, PathStateClosure> cleanPathStateClosureMap) 
  				throws PathFactoryException {
  	
    Table<Path, Path, PathStateClosure> phiNodeTable = HashBasedTable.create();
    
  	Deque<Path> queue = Queues.newArrayDeque();  	
  	queue.push(entPath);
		
		Path retPath = null;
		
		while(!queue.isEmpty()) {
			Path path = queue.pop();
			
			if(path.isFuncRet()) {
				retPath = path; continue;
			}
			
			PathStateClosure currStateClosure;
			
			if(path == entPath) {
				currStateClosure = entStateClosure;
			} else {
				/* Encode the path as path state closure whenever need it */
				PathStateClosure cleanStateClosure;
				
				if(!cleanPathStateClosureMap.containsKey(path)) {
					cleanStateClosure = getPathStateClosure(path);
					cleanPathStateClosureMap.put(path, cleanStateClosure);
				} else {
					cleanStateClosure = cleanPathStateClosureMap.get(path); 
				}
				
				Map<Path, PathStateClosure> phiNode = phiNodeTable.row(path);				
				PathStateClosure preMergeStateClosure = pathStateFactory.
						mergePreStateClosure( phiNode.values());
				
				/* clean phi node for further collection */
				phiNode.clear();
				
				/* substitute state variable of current path */
				currStateClosure = cleanStateClosure.apply(preMergeStateClosure);
			}
			
			if(path.isFuncEnt() && path != entPath) { // nested function call
				Triple<Path, PathStateClosure, Boolean> resFuncTriple = 
						checkReachFuncDFS(graph, label, path, currStateClosure, currIterTimesMap, cleanPathStateClosureMap);
				if(!resFuncTriple.thd()) return Triple.of(null, null, false);
				path = resFuncTriple.fst();
				currStateClosure = resFuncTriple.snd();
			}
			
			IOUtils.out().println(path.stmtsToString());
			
			if(path.hasLabel(label))	{
				IOUtils.out().println("Checking path reachability.");
				StateExpression state = currStateClosure.getPathState();
        SatResult<?> res = pathEncoding.checkPath(state);
        IOUtils.out().println("Result: " + res);
        runIsReachable = res.isSatisfiable();
        if(!runIsReachable) return Triple.of(null, null, false);
        
        if( Preferences.isSet(Preferences.OPTION_COUNTER_EXAMPLE) )
        	IOUtils.out().println("\nCounter-example:\n" + res.getUnknown_reason());
			}
			
      /* find all the successors of path */
			Collection<Path> successors = getSuccessorsViaUnroll(graph, path, currIterTimesMap);

			/* propagate to all successors' phi-node */
			for(Path succ : successors) {
				phiNodeTable.put(succ, path, currStateClosure);
				
				/* Process the path until all its predecessors are encoded */
				int completeSize = getCompleteSize(graph, succ, currIterTimesMap);
				Map<Path, PathStateClosure> succPhiNode = phiNodeTable.row(succ);	
				if(succPhiNode.size() == completeSize) queue.push(succ);
			}
  	}
		
		assert(retPath != null);
		
		/* substitute state variable of current path */
		PathStateClosure cleanStateClosure;
		if(!cleanPathStateClosureMap.containsKey(retPath)) {
			cleanStateClosure = getPathStateClosure(retPath);
			cleanPathStateClosureMap.put(retPath, cleanStateClosure);
		} else {
			cleanStateClosure = cleanPathStateClosureMap.get(retPath); 
		}
		
		Map<Path, PathStateClosure> phiNode = phiNodeTable.row(retPath);		
		PathStateClosure preMergeStateClosure = pathStateFactory.
				mergePreStateClosure( phiNode.values());
		
		/* clean phi node for further collection */
		phiNode.clear();
		
		PathStateClosure currStateClosure = cleanStateClosure.apply(preMergeStateClosure);
		return Triple.of(retPath, currStateClosure, true);
  }

	/**
	 * Propagate state expression to successor paths via BFS, <code>pathStateClosureMap
	 * </code> is passed around state propagate and state propagate in the function
	 * call, cause different function calls may visited the same paths (called the same
	 * functions).
	 * 
	 * @param graph
	 * @return
	 * @throws PathFactoryException 
	 */
	private void checkReachDFSLoopMerge(PathGraph graph, 
			String label, 
			ImmutableMap<Path, Integer> iterTimesMap) 
					throws PathFactoryException {
		
		IOUtils.out().println("\nAnalyzing ...");
		
		Map<Path, Integer> currIterTimesMap = Maps.newHashMap(iterTimesMap);
		Map<Path, PathStateClosure> cleanPathStateClosureMap = Maps.newHashMap();
	  Table<Path, Path, PathStateClosure> phiNodeTable = HashBasedTable.create();
	  /* The order of the add-in pre-states should be kept */
	  Multimap<Path, PathStateClosure> loopExitPostPhiNode = LinkedHashMultimap.create();
		
		Deque<Path> queue = Queues.newArrayDeque();  	
		queue.push(graph.getSrcPath());
		
		while(!queue.isEmpty()) {
			Path path = queue.pop();
			
			IOUtils.out().println(path.stmtsToString());
			
			/* Encode the path as path state closure whenever need it */
			PathStateClosure cleanPathStateClosure;
			
			if(!cleanPathStateClosureMap.containsKey(path)) {
				cleanPathStateClosure = getPathStateClosure(path);
				cleanPathStateClosureMap.put(path, cleanPathStateClosure);
			} else {
				cleanPathStateClosure = cleanPathStateClosureMap.get(path); 
			}
			
			/* Get the path state of current path */
			PathStateClosure currStateClosure;
			
			if(path == graph.getSrcPath()) {
				currStateClosure = cleanPathStateClosure;
			} else {
				if(loopExitMap.containsValue(path)) {
					Collection<PathStateClosure> preStateClosures = loopExitPostPhiNode.get(path);
					Collection<PathStateClosure> postStateClosures = Lists.newArrayListWithExpectedSize(preStateClosures.size());
					for(PathStateClosure preStateClosure : preStateClosures) {
						PathStateClosure postStateClosure = cleanPathStateClosure.apply(preStateClosure);
						postStateClosures.add(postStateClosure);
					}
					/* Resolve the post-state of phi-node to merge the state at the loop exit point */
					currStateClosure = pathStateFactory.mergePreStateClosure(postStateClosures);
					
					/* Clean phi-node for further collection */
					loopExitPostPhiNode.removeAll(path);
					Map<Path, PathStateClosure> phiNode = phiNodeTable.row(path);
					phiNode.clear(); 
					
				} else {
					Map<Path, PathStateClosure> phiNode = phiNodeTable.row(path);				
					PathStateClosure preMergeStateClosure = pathStateFactory.
							mergePreStateClosure( phiNode.values());
					/* clean phi node for further collection */
					phiNode.clear();
					/* substitute state variable of current path */
					currStateClosure = cleanPathStateClosure.apply(preMergeStateClosure);
				}
			}
			
			if(path.isFuncEnt()) {
				Triple<Path, PathStateClosure, Boolean> resFuncTriple = checkReachFuncDFSLoopMerge(
						graph, label, path, currStateClosure, currIterTimesMap, cleanPathStateClosureMap);
				if(!resFuncTriple.thd()) return;
				
				path = resFuncTriple.fst();
				currStateClosure = resFuncTriple.snd();
			}
			
			if(path.hasLabel(label))	{
				IOUtils.out().println("Checking path reachability.");
				StateExpression state = currStateClosure.getPathState();
	      SatResult<?> res = pathEncoding.checkPath(state);
	      IOUtils.out().println("Result: " + res);
	      runIsReachable = res.isSatisfiable();
	      if(!runIsReachable)	return;
	      
	      if( Preferences.isSet(Preferences.OPTION_COUNTER_EXAMPLE) )
	      	IOUtils.out().println("\nCounter-example:\n" + res.getUnknown_reason());
			}
			
			if(path.isLoopEntry()) {
				for(Path loopExitPath : loopExitMap.get(path)) {
					loopExitPostPhiNode.put(loopExitPath, currStateClosure);
				}
			}
			
	    /* find all the successors of path */
			Collection<Path> successors = getSuccessorsViaUnroll(graph, path, currIterTimesMap);
	
			/* propagate to all successors' phi-node */
			for(Path succ : successors) {
				phiNodeTable.put(succ, path, currStateClosure);
				
				/* Process the path until all its predecessors are encoded */
				int completeSize = getCompleteSize(graph, succ, currIterTimesMap);
				Map<Path, PathStateClosure> succPhiNode = phiNodeTable.row(succ);	
				if(succPhiNode.size() == completeSize) queue.push(succ);
			}
		}
	}

	/**
	 * Propagate path state closure of function ent path <code>entPath</code>
	 * to its successors until reach the the function ret path
	 * 
	 * @param graph
	 * @param label
	 * @param entPath
	 * @param entStateClosure 
	 * @param currIterTimesMap
	 * @param cleanPathStateClosureMap
	 * @return
	 * @throws PathFactoryException
	 */
	private Triple<Path, PathStateClosure, Boolean> checkReachFuncDFSLoopMerge(
			PathGraph graph, 
			String label,
			Path entPath,
			PathStateClosure entStateClosure, 
			Map<Path, Integer> currIterTimesMap,
			Map<Path, PathStateClosure> cleanPathStateClosureMap) 
					throws PathFactoryException {
		
	  Table<Path, Path, PathStateClosure> phiNodeTable = HashBasedTable.create();
	  
	  /* The order of the add-in pre-states should be kept */
	  Multimap<Path, PathStateClosure> loopExitPostPhiNode = LinkedHashMultimap.create();
	  
		Deque<Path> queue = Queues.newArrayDeque();  	
		queue.push(entPath);
		
		Path retPath = null;
		
		while(!queue.isEmpty()) {
			Path path = queue.pop();
			
			if(path.isFuncRet()) {
				retPath = path; continue;
			}
			
			PathStateClosure currStateClosure;
			
			if(path == entPath) {
				currStateClosure = entStateClosure;
			} else {
				/* Encode the path as path state closure whenever need it */
				PathStateClosure cleanStateClosure;
				
				if(!cleanPathStateClosureMap.containsKey(path)) {
					cleanStateClosure = getPathStateClosure(path);
					cleanPathStateClosureMap.put(path, cleanStateClosure);
				} else {
					cleanStateClosure = cleanPathStateClosureMap.get(path); 
				}
				
				if(loopExitMap.containsValue(path)) {
					Collection<PathStateClosure> preStateClosures = loopExitPostPhiNode.get(path);
					Collection<PathStateClosure> postStateClosures = Lists.newArrayListWithExpectedSize(preStateClosures.size());
					for(PathStateClosure preStateClosure : preStateClosures) {
						PathStateClosure postStateClosure = cleanStateClosure.apply(preStateClosure);
						postStateClosures.add(postStateClosure);
					}
					/* Resolve the post-state of phi-node to merge the state at the loop exit point */
					currStateClosure = pathStateFactory.mergePreStateClosure(postStateClosures);
					
					/* Clean phi-node for further collection */
					loopExitPostPhiNode.removeAll(path);
					Map<Path, PathStateClosure> phiNode = phiNodeTable.row(path);
					phiNode.clear(); 
		
				} else {
					Map<Path, PathStateClosure> phiNode = phiNodeTable.row(path);				
					PathStateClosure preMergeStateClosure = pathStateFactory.
							mergePreStateClosure( phiNode.values());
					/* clean phi node for further collection */
					phiNode.clear();
					/* substitute state variable of current path */
					currStateClosure = cleanStateClosure.apply(preMergeStateClosure);
				}
			}
			
			if(path.isFuncEnt() && path != entPath) { // nested function call
				Triple<Path, PathStateClosure, Boolean> resFuncTriple = 
						checkReachFuncDFSLoopMerge(graph, label, path, currStateClosure, currIterTimesMap, cleanPathStateClosureMap);
				if(!resFuncTriple.thd()) return Triple.of(null, null, false);
				path = resFuncTriple.fst();
				currStateClosure = resFuncTriple.snd();
			}
			
			IOUtils.out().println(path.stmtsToString());
			
			if(path.hasLabel(label))	{
				IOUtils.out().println("Checking path reachability.");
				StateExpression state = currStateClosure.getPathState();
	      SatResult<?> res = pathEncoding.checkPath(state);
	      IOUtils.out().println("Result: " + res);
	      runIsReachable = res.isSatisfiable();
	      if(!runIsReachable) return Triple.of(null, null, false);
	      
	      if( Preferences.isSet(Preferences.OPTION_COUNTER_EXAMPLE) )
	      	IOUtils.out().println("\nCounter-example:\n" + res.getUnknown_reason());
			}
			
			if(path.isLoopEntry()) {
				for(Path loopExitPath : loopExitMap.get(path)) {
					loopExitPostPhiNode.put(loopExitPath, currStateClosure);
				}
			}
			
	    /* find all the successors of path */
			Collection<Path> successors = getSuccessorsViaUnroll(graph, path, currIterTimesMap);
	
			/* propagate to all successors' phi-node */
			for(Path succ : successors) {
				phiNodeTable.put(succ, path, currStateClosure);
				
				/* Process the path until all its predecessors are encoded */
				int completeSize = getCompleteSize(graph, succ, currIterTimesMap);
				Map<Path, PathStateClosure> succPhiNode = phiNodeTable.row(succ);	
				if(succPhiNode.size() == completeSize) queue.push(succ);
			}
		}
		
		assert(retPath != null);
		
		/* substitute state variable of current path */
		PathStateClosure cleanStateClosure;
		if(!cleanPathStateClosureMap.containsKey(retPath)) {
			cleanStateClosure = getPathStateClosure(retPath);
			cleanPathStateClosureMap.put(retPath, cleanStateClosure);
		} else {
			cleanStateClosure = cleanPathStateClosureMap.get(retPath); 
		}
		
		Map<Path, PathStateClosure> phiNode = phiNodeTable.row(retPath);		
		PathStateClosure preMergeStateClosure = pathStateFactory.
				mergePreStateClosure( phiNode.values());
		
		/* clean phi node for further collection */
		phiNode.clear();
		
		PathStateClosure currStateClosure = cleanStateClosure.apply(preMergeStateClosure);
		
		return Triple.of(retPath, currStateClosure, true);
	}

	/**
	 * Get the path state closure for <code>path</code> with empty state as previous state var
	 * @param path
	 * @return the clean path state closure of path
	 * @throws PathFactoryException
	 */
	private PathStateClosure getPathStateClosure(Path path) throws PathFactoryException {
		StateExpression stateVar = pathEncoding.emptyState();
		stateVar.setProperty(Identifiers.SRCPATH, path);
		StateExpression pathState = encodePathWithPreState(path, stateVar);
		return pathStateFactory.suspend(pathState, Collections.singletonList(stateVar));
  }
  
  /**
   * Get the successors of <code>path</code> in the <code>graph</code>
   * If <code>path</code> is not loop entry, just return its successors.
   * If <code>path</code> is a loop entry, during loop iteration, just
   * return its out path (the path out-going into the loop body). Once
   * the iteration is finished, return its exit path (that path exit the
   * loop). The <code>currIterTimesMap</code> got updated after one 
   * iteration.
   * 
   * @param graph
   * @param path
   * @param currIterTimesMap
   * @return
   */
  private Collection<Path> getSuccessorsViaUnroll(
  		PathGraph graph, 
  		Path path, 
  		Map<Path, Integer> currIterTimesMap) {
  	
  	if(!currIterTimesMap.containsKey(path)) { // non-loop entry
			return graph.getSuccessorMap().get(path);			
		}
  	
  	int currIterTimes = currIterTimesMap.get(path);
			
  	/* Unrolling is not finished yet, add out paths only */
  	if(currIterTimes > 0) {
  		currIterTimesMap.put(path, currIterTimes-1);	
  		return loopEnterMap.get(path);
  	} 
			
  	/* Unrolling is finished, add exit paths only, reset iteration times */
  	int iterTimes = path.getIterTimes();
  	currIterTimesMap.put(path, iterTimes);
				
  	return loopExitMap.get(path);
  }
  
  /**
   * Get the full size of predecessors of path <code>succ</code>. 
   * If it is not a loop entry, just return its predecessors' size.
   * If so, before the loop iteration, return the number of init
   * path (the path from loop init block to loop block); during the
   * loop iteration, return the number of back paths (the path from
   * the end of loop body to the loop entry).
   * 
   * @param graph
   * @param succ
   * @param iterTimesMap
   * @return
   */
  private int getCompleteSize(PathGraph graph, Path succ, 
  		Map<Path, Integer> iterTimesMap) {
		if(!iterTimesMap.containsKey(succ)) // loop entry
			return graph.getPredecessorMap().get(succ).size();
		
		int currIterTimes = iterTimesMap.get(succ);
		int iterTimes = succ.getIterTimes();
				
		if(currIterTimes < iterTimes) { // unrolling happened
			Collection<Path> backPaths = loopBackMap.get(succ);
	  	return backPaths.size();
		}
		
		/* unrolling not happened yet */
    Collection<Path> entryPaths = loopInitMap.get(succ);
		return entryPaths.size();
  }
	
  /**
   * Propagate path state closure of function ent path <code>entPath</code>
   * to its successors until reach the the function ret path
   * 
   * @param graph
   * @param entPath
   * @param entPathStateClosure
   * @param currIterTimesMap
   * @param cleanPathStateClosureMap
   * @param assertPreCondMap
   * @return
   * @throws PathFactoryException
   */
  private Triple<Path, PathStateClosure, Boolean> statePropagateFuncDFS(
  		PathGraph graph, 
  		Path entPath,
  		PathStateClosure entPathStateClosure, 
  		Map<Path, Integer> currIterTimesMap,
  		Map<Path, PathStateClosure> cleanPathStateClosureMap,
  		Map<Path, StateExpressionClosure> assertPreCondMap) 
  				throws PathFactoryException {
  	
  	ExpressionEncoder encoder = pathEncoding.getExpressionEncoder();
    Table<Path, Path, PathStateClosure> phiNodeTable = HashBasedTable.create();
    
  	Deque<Path> queue = Queues.newArrayDeque();  	
  	queue.push(entPath);
		
		Path retPath = null;
		
		while(!queue.isEmpty()) {
			Path path = queue.pop();
			
			IOUtils.out().println(path.stmtsToString());
			if(path.isFuncRet()) {
				retPath = path; continue;
			}
			
			PathStateClosure currPathStateClosure;
			
			if(path == entPath) {
				currPathStateClosure = entPathStateClosure;
			} else {
				/* Encode the path as path state closure whenever need it */
				PathStateClosure cleanPathStateClosure;
				
				if(!cleanPathStateClosureMap.containsKey(path)) {
					cleanPathStateClosure = getPathStateClosure(path);
					cleanPathStateClosureMap.put(path, cleanPathStateClosure);
				} else {
					cleanPathStateClosure = cleanPathStateClosureMap.get(path); 
				}
				
				Map<Path, PathStateClosure> phiNode = phiNodeTable.row(path);				
				PathStateClosure preMergeStateClosure = pathStateFactory.
						mergePreStateClosure( phiNode.values());
				
				/* clean phi node for further collection */
				phiNode.clear();
				
				/* substitute state variable of current path */
				currPathStateClosure = cleanPathStateClosure.apply(preMergeStateClosure);
			}
			
			if(path.isFuncEnt() && path != entPath) { // nested function call
				Triple<Path, PathStateClosure, Boolean> resFuncTriple = 
						statePropagateFuncDFS(graph, path, currPathStateClosure, currIterTimesMap, cleanPathStateClosureMap, assertPreCondMap);
				if(!resFuncTriple.thd()) return Triple.of(null, null, false);
				path = resFuncTriple.fst();
				currPathStateClosure = resFuncTriple.snd();
			}
			
			/* collect assertion path */
			if(path.isAssertPath())	{
				IOUtils.out().println("Checking... ");
				StateExpressionClosure preCond;
				if(assertPreCondMap.containsKey(path)) {
					preCond = assertPreCondMap.get(path);
				} else {
					preCond = path.getStmt(path.getSize() - 1).getPreCondition(encoder);
					assertPreCondMap.put(path, preCond);
				}
				boolean success = processAssertion(currPathStateClosure, preCond);
				if(!success) return Triple.of(null, null, false);
			}
			
      /* find all the successors of path */
			Collection<Path> successors = getSuccessorsViaUnroll(graph, path, currIterTimesMap);

			/* propagate to all successors' phi-node */
			for(Path succ : successors) {
				phiNodeTable.put(succ, path, currPathStateClosure);
				
				/* Process the path until all its predecessors are encoded */
				int completeSize = getCompleteSize(graph, succ, currIterTimesMap);
				Map<Path, PathStateClosure> succPhiNode = phiNodeTable.row(succ);	
				if(succPhiNode.size() == completeSize) queue.push(succ);
			}
  	}
		
		assert(retPath != null);
		
		/* substitute state variable of current path */
		PathStateClosure cleanPathStateClosure;
		
		if(!cleanPathStateClosureMap.containsKey(retPath)) {
			cleanPathStateClosure = getPathStateClosure(retPath);
			cleanPathStateClosureMap.put(retPath, cleanPathStateClosure);
		} else {
			cleanPathStateClosure = cleanPathStateClosureMap.get(retPath); 
		}
		
		Map<Path, PathStateClosure> phiNode = phiNodeTable.row(retPath);		
		PathStateClosure preMergeStateClosure = pathStateFactory.
				mergePreStateClosure( phiNode.values());
		
		/* clean phi node for further collection */
		phiNode.clear();
		
		PathStateClosure currStateClosure = cleanPathStateClosure.apply(preMergeStateClosure);
		
		return Triple.of(retPath, currStateClosure, true);
  }
  
  /**
   * Propagate state expression to successor paths via BFS, <code>pathStateClosureMap
   * </code> and <code>assertPreCondMap</code> are passed around state propagate and 
   * state propagate in the function call, cause function calls may nested in the loop
   * body, we may visit the same paths of the same function call multiple times
   * 
   * @param graph
   * @param iterTimesMap 
   * @return
   * @throws PathFactoryException 
   */
  private void statePropagateDFS(PathGraph graph, 
  		ImmutableMap<Path, Integer> iterTimesMap) 
  				throws PathFactoryException {
  	
  	IOUtils.out().println("\nAnalyzing ...");
  	
  	ExpressionEncoder encoder = pathEncoding.getExpressionEncoder();
  	
  	Map<Path, Integer> currIterTimesMap = Maps.newHashMap(iterTimesMap);
  	Map<Path, PathStateClosure> cleanPathStateClosureMap = Maps.newHashMap();
  	Map<Path, StateExpressionClosure> assertPreCondMap = Maps.newHashMap();
    Table<Path, Path, PathStateClosure> phiNodeTable = HashBasedTable.create();
  	
  	Deque<Path> queue = Queues.newArrayDeque();  	
  	queue.push(graph.getSrcPath());
  	
  	while(!queue.isEmpty()) {
  		Path path = queue.pop();
			
			/* Encode the path as path state closure whenever need it */
			PathStateClosure cleanPathStateClosure;
			IOUtils.out().println(path.stmtsToString());
			
			if(!cleanPathStateClosureMap.containsKey(path)) {
				cleanPathStateClosure = getPathStateClosure(path);
				cleanPathStateClosureMap.put(path, cleanPathStateClosure);
			} else {
				cleanPathStateClosure = cleanPathStateClosureMap.get(path); 
			}
			
			/* Get the current path state of current path */
			PathStateClosure currPathStateClosure;
			
			if(path == graph.getSrcPath()) {
				currPathStateClosure = cleanPathStateClosure;
			} else {
				
				Map<Path, PathStateClosure> phiNode = phiNodeTable.row(path);
				PathStateClosure preMergeStateClosure = pathStateFactory.
						mergePreStateClosure( phiNode.values());
				
				/* clean phi node for further collection */
				phiNode.clear();
				
				/* substitute state variable of current path */
				currPathStateClosure = cleanPathStateClosure.apply(preMergeStateClosure);
			}
  		
			if(path.isFuncEnt()) {
				Triple<Path, PathStateClosure, Boolean> resFuncTriple = statePropagateFuncDFS(
						graph, path, currPathStateClosure, currIterTimesMap, cleanPathStateClosureMap, assertPreCondMap);
				if(!resFuncTriple.thd()) return;
				
				path = resFuncTriple.fst();
				currPathStateClosure = resFuncTriple.snd();
			}
  		
			/* collect assertion path */
			if(path.isAssertPath())	{
				IOUtils.out().println("Checking... ");
				StateExpressionClosure preCond;
				if(assertPreCondMap.containsKey(path)) {
					preCond = assertPreCondMap.get(path);
				} else {
					preCond = path.getStmt(path.getSize() - 1).getPreCondition(encoder);
					assertPreCondMap.put(path, preCond);
				}
				boolean success = processAssertion(currPathStateClosure, preCond);
				if(!success) break;
			}
			
      /* find all the successors of path */
			Collection<Path> successors = getSuccessorsViaUnroll(graph, path, currIterTimesMap);

			/* propagate to all successors' phi-node */
			for(Path succ : successors) {
				phiNodeTable.put(succ, path, currPathStateClosure);
				
				/* Process the path until all its predecessors are encoded */
				int completeSize = getCompleteSize(graph, succ, currIterTimesMap);
				Map<Path, PathStateClosure> succPhiNode = phiNodeTable.row(succ);	
				if(succPhiNode.size() == completeSize) queue.push(succ);
			}
  	}
  }

  /**
   * Check the current statement's pre-condition 
   * 
   * @param preCond
   * @param pre
   * @return false if the statement results in an invalid verification condition
   *         or an infeasible path; true otherwise.
   */
  private boolean checkPreCondition(StateExpression preCond, StateExpressionClosure pre) 
      throws PathFactoryException {
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
              IOUtils.out().println("\nCounter-example:\n" + result.getCounterExampleToString());
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
 
  /** Encode statement <code>stmt</code>, with single <code>preCondition</code> */
  private StateExpression encodeStatement(IRStatement stmt, StateExpression preCondition) 
      throws PathFactoryException {
    /* Precondition is OK, encode the postcondition. */
    StateExpression  postCond = stmt.getPostCondition(pathEncoding, preCondition);
    if(IOUtils.debugEnabled())
      IOUtils.debug().pln("Post-condition:\n" + postCond).flush();
    return postCond;
  }
  
  /**
   * Encode an edge path <code>currPath</code> with a <code>preState</code>
   * @param currPath
   * @param preState
   * @return
   * @throws PathFactoryException
   */
  private StateExpression encodeEdgePath(Path currPath, StateExpression preState) 
  		throws PathFactoryException {
  	Preconditions.checkArgument(currPath.getSize() == 1);
		IRStatement stmt = currPath.getStmt(0);
		StateExpression currState = encodeStatement(stmt, preState);
		currState.addGuard(currState.getConstraint());
  	return currState;
  }
  
  /**
   * Encode an non-edge path <code>currPath</code> with a <code>preState</code>
   * @param currPath
   * @param preState
   * @return
   * @throws PathFactoryException
   */
  private StateExpression encodeNonEdgePath(Path currPath, StateExpression preState) 
  		throws PathFactoryException {
  	StateExpression currState = preState;
    for(IRStatement stmt : currPath.getStmts()) {
    	currState = encodeStatement(stmt, currState);
    }
    return currState;
  }
  
  /**
   * Encode a path <code>currPath</code> with a <code>preState</code>
   * @param currPath
   * @param preState
   * @return
   * @throws PathFactoryException
   */
  private StateExpression encodePathWithPreState(Path currPath, StateExpression preState) 
  		throws PathFactoryException {
  	if(currPath.isEmpty()) return preState;
  	
  	if(currPath.isEdgePath()) // edge path
  		return encodeEdgePath(currPath, preState);
  	else 
  		return encodeNonEdgePath(currPath, preState);
  }
  
  /** Checking assertion path <code>preCondition</code> with path state closure <code>closure</code> */
  private boolean processAssertion(PathStateClosure closure, StateExpressionClosure preCondition) 
  		throws PathFactoryException {
	  boolean succeed = checkPreCondition(closure.getPathState(), preCondition);
	  if(succeed) {
	  	if (runIsValid() && !runIsFeasible())
	  		IOUtils.err().println("WARNING: path assumptions are unsatisfiable");
	  }
	  return succeed;
  }

  /**
	 * Pre-process <code>graph</code> via BFS with <code>preprocessor</code>,
	 * is used to select successors path during DFS
	 * 
	 * @param preprocessor
	 * @param graph
	 * @return
	 */
	private void preprocessDFS(PreProcessor<?> preprocessor, 
			PathGraph graph,
			ImmutableMap<Path, Integer> iterTimesMap) {
		
  	Map<Path, Integer> currIterTimesMap = Maps.newHashMap(iterTimesMap);
		Multimap<Path, Path> phiNodeMap = HashMultimap.create();
		
		Deque<Path> queue = Queues.newArrayDeque();  	
		queue.push(graph.getSrcPath());
		
		while(!queue.isEmpty()) {
			Path path = queue.pop();
			
			if(path.isFuncEnt()) {
				path = preprocessFuncDFS(preprocessor, graph, path, currIterTimesMap);
			}
			
			IOUtils.out().println("Preprocess " + path.stmtsToString());
			
			/* pre-process the current path */
	    for(IRStatement stmt : path.getStmts()) preprocessor.analysis(stmt);
	    
			/* clean pre-process phi-node for further collection */
	    phiNodeMap.removeAll(path);
			
	    /* find all the successors of path */
			Collection<Path> successors = getSuccessorsViaUnroll(graph, path, currIterTimesMap);
	
			/* filter the successors with complete phi node and add to the queue */
			for(Path succ : successors) {
				phiNodeMap.put(succ, path);
				int completeSize = getCompleteSize(graph, succ, currIterTimesMap);
				Collection<Path> succPhiNode = phiNodeMap.get(succ);	
				
				/* Process the path until all its predecessors are pre-processed */
				if(succPhiNode.size() == completeSize) queue.push(succ);
			}
		}
	}

	/**
	 * Pre-process the function ent path <code>entPath</code> in <code>graph</code>,
	 * used <code>preprocessor</code>, to its successors until reach the the function 
	 * ret path.
	 * 
	 * @param preprocessor
	 * @param graph
	 * @param entPath
	 * @param currIterTimesMap
	 * @return retPath
	 */
	private Path preprocessFuncDFS(
			PreProcessor<?> preprocessor,
			PathGraph graph, 
			Path entPath,
			Map<Path, Integer> currIterTimesMap) {
		Multimap<Path, Path> phiNodeMap = HashMultimap.create();
		Deque<Path> queue = Queues.newArrayDeque();  	
		queue.push(entPath);
		
		Path retPath = null;
		
		while(!queue.isEmpty()) {
			Path path = queue.pop();
			
			if(path.isFuncRet()) {
				retPath = path; continue;
			}
			
			if(path.isFuncEnt() && path != entPath) { // nested function call
				path = preprocessFuncDFS(preprocessor, graph, path, currIterTimesMap);
			}
			
			IOUtils.out().println("Preprocess " + path.stmtsToString());
			
			/* pre-process the current path */
	    for(IRStatement stmt : path.getStmts())	preprocessor.analysis(stmt);
	    
			/* clean preprocess phi-node for further collection */
	    phiNodeMap.removeAll(path);
			
	    /* find all the successors of path */
			Collection<Path> successors = getSuccessorsViaUnroll(graph, path, currIterTimesMap);
			
			/* filter the successors with complete phi node and add to the queue */
			for(Path succ : successors) {
				phiNodeMap.put(succ, path);
				int completeSize = getCompleteSize(graph, succ, currIterTimesMap);
				Collection<Path> succPhiNode = phiNodeMap.get(succ);	
				
				/* Process the path until all its predecessors are pre-processed */
				if(succPhiNode.size() == completeSize) queue.push(succ);
			}
		}
		assert(retPath != null);
		return retPath;
	}
}
