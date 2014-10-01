package edu.nyu.cascade.c;

import java.util.Collection;
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
import edu.nyu.cascade.ir.expr.PathFactoryException;
import edu.nyu.cascade.ir.path.PathEncoding;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateExpressionClosure;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.Triple;

/**
 * Encodes a program path as a verification condition and checks the condition
 * for validity. Also optionally checks the path for feasibility (e.g., the path
 * (x := 0; assume x > 0; assert false) is invalid but infeasible).
 */

class PathMergeEncoder implements PathEncoder<PathGraph> {
  private final PathEncoding pathEncoding;
  private final Stopwatch timer;
  private boolean runIsValid, runIsFeasible, runIsReachable, checkFeasibility;
  private Multimap<Path, Path> loopExitMap, loopEnterMap, loopInitMap, loopBackMap;
  
  private PathMergeEncoder(PathEncoding pathEncoding) {
    this.pathEncoding = pathEncoding;
    this.timer = Stopwatch.createUnstarted();
    checkFeasibility = false;
    reset();
  }

  static PathMergeEncoder create(PathEncoding encoding) {
    return new PathMergeEncoder(encoding);
  }
  
  @Override
  public void reset() {
    runIsValid = true;
    runIsFeasible = true;
    runIsReachable = false;
  }
  
  @Override
  public boolean runIsFeasible() {
    return runIsFeasible;
  }
  
  @Override
  public boolean runIsReachable() {
  	return runIsReachable;
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
		
  	/* Pre-processing for mode Partition and Burstall */
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
  public void checkReach(PreProcessor<?> preprocessor, 
  		PathGraph graph, 
  		String label) throws PathFactoryException {
  	Preconditions.checkArgument(graph.isValid());
  	
		/* label the exit paths and entry paths for every loop entry */
		List<Multimap<Path, Path>> loopRoadMap = PathGraph.getLoopInfo(graph);
		loopInitMap = loopRoadMap.get(0);
		loopEnterMap = loopRoadMap.get(1);
	  loopBackMap = loopRoadMap.get(2);
		loopExitMap = loopRoadMap.get(3);
		
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

	private void checkReachDFS(PathGraph graph, String label, 
			ImmutableMap<Path, Integer> iterTimesMap) 
			throws PathFactoryException {
		
		/* Preparation */
		
		Table<Path, Path, StateExpression> phiNodeTable = HashBasedTable.create();
	  Map<Path, Integer> currIterTimesMap = Maps.newHashMap(iterTimesMap);
	  
	  Path srcPath = graph.getSrcPath();
	  
		Deque<Path> queue = Queues.newArrayDeque();
		queue.push(srcPath);
		
		while(!queue.isEmpty()) {
			Path path = queue.pop();
			
			StateExpression preState;
			if(path == graph.getSrcPath()) {
				preState = pathEncoding.emptyState();
			} else {
				/* Resolve the phi-node to get the pre-state of join point */
				Map<Path, StateExpression> phiNode = phiNodeTable.row(path);
				preState = pathEncoding.noop(phiNode.values());
				phiNode.clear();
			}
			
			Pair<StateExpression, Boolean> pathStatePair = encodePathWithPreState(path, preState);
			if(!pathStatePair.snd())	return;
			StateExpression state = pathStatePair.fst();
			
			if(path.isFuncEnt()) { // nested function call
				Triple<Path, StateExpression, Boolean> resFuncTriple = 
						checkReachFuncDFS(graph, label, path, state, currIterTimesMap);
				if(!resFuncTriple.thd()) return;
				
				path = resFuncTriple.fst(); // path is the function return path
				state = resFuncTriple.snd();
			}
			
			if(path.hasLabel(label)) {
        IOUtils.out().println("Checking path reachability.");
        SatResult<?> res = pathEncoding.checkPath(state);
        IOUtils.out().println("Result: " + res);
        runIsReachable = res.isSatisfiable();
        if(!runIsReachable) return;
        
        if( Preferences.isSet(Preferences.OPTION_COUNTER_EXAMPLE) )
        	IOUtils.out().println("\nCounter-example:\n" + res.getUnknown_reason());
			}
	  	
	    /* find all the successors of path */
			Collection<Path> succs = getSuccessorsViaUnroll(graph, path, currIterTimesMap);
			
	    for(Path succ : succs) {
	    	phiNodeTable.put(succ, path, state);
	    	
				int preExprSize = phiNodeTable.row(succ).size();
				int predecessorSize = getCompleteSize(graph, succ, currIterTimesMap);
				
				/* Do not encode the path until all its predecessors are encoded 
				 * note that the graph is acyclic in merged encode 
				 */
				if(preExprSize == predecessorSize) queue.push(succ);
	    }
		}
	}
	
	/**
   * Encode the function graph, return the function return path,
   * the return state, and the last assertion checking result (if
   * <code>false</code>, no need to proceed further checking)
   * 
   * @param graph
   * @param entPath
   * @param preEntState
   * @param currIterTimesMap 
   * @return
   * @throws PathFactoryException
   */
  private Triple<Path, StateExpression, Boolean> checkReachFuncDFS(
  		PathGraph graph, 
  		String label,
			Path entPath, 
			StateExpression entState,
			Map<Path, Integer> currIterTimesMap) 
					throws PathFactoryException {
  	
  	Table<Path, Path, StateExpression> phiNodeTable = HashBasedTable.create();

		Deque<Path> queue = Queues.newArrayDeque();
		queue.push(entPath);
		
		Path retPath = null;
		
		while(!queue.isEmpty()) {
			Path path = queue.pop();
			
			if(path.isFuncRet()) {
				retPath = path; continue;
			}
			
			StateExpression state;
			
			if(path == entPath) {
				state = entState;
			} else {
				/* Resolve the phi-node to get the pre-state of join point */
				Map<Path, StateExpression> phiNode = phiNodeTable.row(path);
				StateExpression preState = pathEncoding.noop(phiNode.values());
				phiNode.clear();
				Pair<StateExpression, Boolean> pathStatePair = encodePathWithPreState(path, preState);
				state = pathStatePair.fst();
			}
			
			if(path.isFuncEnt() && path != entPath) { // nested function call
				Triple<Path, StateExpression, Boolean> resFuncTriple = 
						checkReachFuncDFS(graph, label, path, state, currIterTimesMap);
				if(!resFuncTriple.thd()) return Triple.of(null, null, false);
				
				path = resFuncTriple.fst(); // path is the function return path
				state = resFuncTriple.snd();
			}
			
			if(path.hasLabel(label)) {
        IOUtils.out().println("Checking path reachability.");
        SatResult<?> res = pathEncoding.checkPath(state);
        IOUtils.out().println("Result: " + res);
        runIsReachable = res.isSatisfiable();
        if(!runIsReachable) return Triple.of(null, null, false);
        
        if( Preferences.isSet(Preferences.OPTION_COUNTER_EXAMPLE) )
        	IOUtils.out().println("\nCounter-example:\n" + res.getUnknown_reason());
			}
    	
      /* find all the successors of path */
			Collection<Path> succs = getSuccessorsViaUnroll(graph, path, currIterTimesMap);
			
			for(Path succ : succs) {
	    	phiNodeTable.put(succ, path, state);
	    	
				int preExprSize = phiNodeTable.row(succ).size();
				int predecessorSize = getCompleteSize(graph, succ, currIterTimesMap);
				
				/* Do not encode the path until all its predecessors are encoded 
				 * note that the graph is acyclic in merged encode 
				 */
				if(preExprSize == predecessorSize) queue.push(succ);
	    }
		}
		
		assert(retPath != null);
		
		/* Resolve the phi-node to get the pre-state of join point */
		Map<Path, StateExpression> phiNode = phiNodeTable.row(retPath);
		StateExpression preState = pathEncoding.noop(phiNode.values());
		phiNode.clear();
		Pair<StateExpression, Boolean> pathStatePair = encodePathWithPreState(retPath, preState);
		return Triple.of(retPath, pathStatePair.fst(), pathStatePair.snd());
	}
  
  private void checkReachDFSLoopMerge(PathGraph graph, String label, 
			ImmutableMap<Path, Integer> iterTimesMap) 
			throws PathFactoryException {
		
		/* Preparation */
		
		Table<Path, Path, StateExpression> phiNodeTable = HashBasedTable.create();
		/* The order of the add-in pre-states should be kept */
		Multimap<Path, StateExpression> loopExitPostPhiNode = LinkedHashMultimap.create();
	  Map<Path, Integer> currIterTimesMap = Maps.newHashMap(iterTimesMap);
	  
	  Path srcPath = graph.getSrcPath();
	  
		Deque<Path> queue = Queues.newArrayDeque();
		queue.push(srcPath);
		
		while(!queue.isEmpty()) {
			Path path = queue.pop();
			
			StateExpression state;
			if(path == graph.getSrcPath()) {
				StateExpression preState = pathEncoding.emptyState();
				Pair<StateExpression, Boolean> pathStatePair = encodePathWithPreState(path, preState);
				state = pathStatePair.fst();
			} else {
				if(loopExitMap.containsValue(path)) {
					Collection<StateExpression> preStates = loopExitPostPhiNode.get(path);
					Collection<StateExpression> postStates = Lists.newArrayListWithExpectedSize(preStates.size());
					for(StateExpression preState : preStates) {
						Pair<StateExpression, Boolean> pathStatePair = encodePathWithPreState(path, preState);
						StateExpression postState = pathStatePair.fst();
						postStates.add(postState);
					}
					
					/* Resolve the post-state of phi-node to merge the state at the loop exit point */
					state = pathEncoding.noop(postStates);
					
					/* Clean phi-node for further collection */
					loopExitPostPhiNode.removeAll(path);
					Map<Path, StateExpression> phiNode = phiNodeTable.row(path);
					phiNode.clear(); 
		
				} else {
					/* Resolve the phi-node to get the pre-state of join point */
					Map<Path, StateExpression> phiNode = phiNodeTable.row(path);
					StateExpression preState = pathEncoding.noop(phiNode.values());
					phiNode.clear();
					
					Pair<StateExpression, Boolean> pathStatePair = encodePathWithPreState(path, preState);
					state = pathStatePair.fst();
				}
			}
			
			if(path.isFuncEnt()) { // nested function call
				Triple<Path, StateExpression, Boolean> resFuncTriple = 
						checkReachFuncDFSLoopMerge(graph, label, path, state, currIterTimesMap);
				if(!resFuncTriple.thd()) return;
				
				path = resFuncTriple.fst(); // path is the function return path
				state = resFuncTriple.snd();
			}
			
			if(path.hasLabel(label)) {
	      IOUtils.out().println("Checking path reachability.");
	      SatResult<?> res = pathEncoding.checkPath(state);
	      IOUtils.out().println("Result: " + res);
	      runIsReachable = res.isSatisfiable();
	      if(!runIsReachable) return;
	      
	      if( Preferences.isSet(Preferences.OPTION_COUNTER_EXAMPLE) )
	      	IOUtils.out().println("\nCounter-example:\n" + res.getUnknown_reason());
			}
			
			if(path.isLoopEntry()) {
				for(Path loopExitPath : loopExitMap.get(path)) {
					loopExitPostPhiNode.put(loopExitPath, state);
				}
			}
	  	
	    /* find all the successors of path */
			Collection<Path> succs = getSuccessorsViaUnroll(graph, path, currIterTimesMap);
			
	    for(Path succ : succs) {
	    	phiNodeTable.put(succ, path, state);
	    	
				/* Do not encode the path until all its predecessors are encoded 
				 * note that the graph is acyclic in merged encode 
				 */
				int preExprSize = phiNodeTable.row(succ).size();
				int predecessorSize = getCompleteSize(graph, succ, currIterTimesMap);
				if(preExprSize == predecessorSize) queue.push(succ);
	    }
		}
	}
  
	private Triple<Path, StateExpression, Boolean> checkReachFuncDFSLoopMerge(
			PathGraph graph, 
			String label,
			Path entPath, 
			StateExpression entState,
			Map<Path, Integer> currIterTimesMap) 
					throws PathFactoryException {
		
		Table<Path, Path, StateExpression> phiNodeTable = HashBasedTable.create();
		/* The order of the add-in pre-states should be kept */
		Multimap<Path, StateExpression> loopExitPostPhiNode = LinkedHashMultimap.create();
	
		Deque<Path> queue = Queues.newArrayDeque();
		queue.push(entPath);
		
		Path retPath = null;
		
		while(!queue.isEmpty()) {
			Path path = queue.pop();
			
			if(path.isFuncRet()) {
				retPath = path; continue;
			}
			
			StateExpression state;
			
			if(path == entPath) {
				state = entState;
			} else {
				if(loopExitMap.containsValue(path)) {
					Collection<StateExpression> preStates = loopExitPostPhiNode.get(path);
					Collection<StateExpression> postStates = Lists.newArrayListWithExpectedSize(preStates.size());
					for(StateExpression preState : preStates) {
						Pair<StateExpression, Boolean> pathStatePair = encodePathWithPreState(path, preState);
						StateExpression postState = pathStatePair.fst();
						postStates.add(postState);
					}
					/* Resolve the post-state of phi-node to merge the state at the loop exit point */
					state = pathEncoding.noop(postStates);
					
					/* Clean phi-node for further collection */
					loopExitPostPhiNode.removeAll(path);
					Map<Path, StateExpression> phiNode = phiNodeTable.row(path);
					phiNode.clear(); 
		
				} else {
					/* Resolve the phi-node to get the pre-state of join point */
					Map<Path, StateExpression> phiNode = phiNodeTable.row(path);
					StateExpression preState = pathEncoding.noop(phiNode.values());
					phiNode.clear();
					Pair<StateExpression, Boolean> pathStatePair = encodePathWithPreState(path, preState);
					state = pathStatePair.fst();
				}
			}
			
			if(path.isFuncEnt() && path != entPath) { // nested function call
				Triple<Path, StateExpression, Boolean> resFuncTriple = 
						checkReachFuncDFSLoopMerge(graph, label, path, state, currIterTimesMap);
				if(!resFuncTriple.thd()) return Triple.of(null, null, false);
				
				path = resFuncTriple.fst(); // path is the function return path
				state = resFuncTriple.snd();
			}
			
			if(path.hasLabel(label)) {
	      IOUtils.out().println("Checking path reachability.");
	      SatResult<?> res = pathEncoding.checkPath(state);
	      IOUtils.out().println("Result: " + res);
	      runIsReachable = res.isSatisfiable();
	      if(!runIsReachable) return Triple.of(null, null, false);
	      
	      if( Preferences.isSet(Preferences.OPTION_COUNTER_EXAMPLE) )
	      	IOUtils.out().println("\nCounter-example:\n" + res.getUnknown_reason());
			}
			
			if(path.isLoopEntry()) {
				for(Path loopExitPath : loopExitMap.get(path)) {
					loopExitPostPhiNode.put(loopExitPath, state);
				}
			}
			
	    /* find all the successors of path */
			Collection<Path> succs = getSuccessorsViaUnroll(graph, path, currIterTimesMap);
			
			for(Path succ : succs) {
				phiNodeTable.put(succ, path, state);
	    	
				/* Do not encode the path until all its predecessors are encoded 
				 * note that the graph is acyclic in merged encode 
				 */
				int preExprSize = phiNodeTable.row(succ).size();
				int predecessorSize = getCompleteSize(graph, succ, currIterTimesMap);
				if(preExprSize == predecessorSize) queue.push(succ);
	    }
		}
		
		assert(retPath != null);
		
		/* Resolve the phi-node to get the pre-state of join point */
		Map<Path, StateExpression> phiNode = phiNodeTable.row(retPath);
		StateExpression preState = pathEncoding.noop(phiNode.values());
		phiNode.clear();
		Pair<StateExpression, Boolean> pathStatePair = encodePathWithPreState(retPath, preState);
		return Triple.of(retPath, pathStatePair.fst(), pathStatePair.snd());
	}

	private void statePropagateDFS(PathGraph graph,
  		ImmutableMap<Path, Integer> iterTimesMap) 
  				throws PathFactoryException {
		
		/* Preparation */
		
		Table<Path, Path, StateExpression> phiNodeTable = HashBasedTable.create();
	  Map<Path, Integer> currIterTimesMap = Maps.newHashMap(iterTimesMap);
	  
	  Path srcPath = graph.getSrcPath();
	  
		Deque<Path> queue = Queues.newArrayDeque();
		queue.push(srcPath);
		
		while(!queue.isEmpty()) {
			Path path = queue.pop();
			
			StateExpression preState;
			if(path == graph.getSrcPath()) {
				preState = pathEncoding.emptyState();
			} else {
				/* Resolve the phi-node to get the pre-state of join point */
				Map<Path, StateExpression> phiNode = phiNodeTable.row(path);
				preState = pathEncoding.noop(phiNode.values());
				phiNode.clear();
			}
			
			Pair<StateExpression, Boolean> pathStatePair = encodePathWithPreState(path, preState);
			if(!pathStatePair.snd())	return;
			StateExpression state = pathStatePair.fst();
			
			if(path.isFuncEnt()) { // nested function call
				Triple<Path, StateExpression, Boolean> resFuncTriple = 
						statePropagateFuncDFS(graph, path, state, currIterTimesMap);
				if(!resFuncTriple.thd()) return;
				
				path = resFuncTriple.fst(); // path is the function return path
				state = resFuncTriple.snd();
			}
	  	
	    /* find all the successors of path */
			Collection<Path> succs = getSuccessorsViaUnroll(graph, path, currIterTimesMap);
			
	    for(Path succ : succs) {
	    	phiNodeTable.put(succ, path, state);
	    	
				int preExprSize = phiNodeTable.row(succ).size();
				int predecessorSize = getCompleteSize(graph, succ, currIterTimesMap);
				
				/* Do not encode the path until all its predecessors are encoded 
				 * note that the graph is acyclic in merged encode 
				 */
				if(preExprSize == predecessorSize) queue.push(succ);
	    }
		}
	}

	/**
   * Encode the function graph, return the function return path,
   * the return state, and the last assertion checking result (if
   * <code>false</code>, no need to proceed further checking)
   * 
   * @param graph
   * @param entPath
   * @param preEntState
   * @param currIterTimesMap 
   * @return
   * @throws PathFactoryException
   */
  private Triple<Path, StateExpression, Boolean> statePropagateFuncDFS(
  		PathGraph graph, 
			Path entPath, 
			StateExpression entState,
			Map<Path, Integer> currIterTimesMap) throws PathFactoryException {
  	
  	Table<Path, Path, StateExpression> phiNodeTable = HashBasedTable.create();

		Deque<Path> queue = Queues.newArrayDeque();
		queue.push(entPath);
		
		Path retPath = null;
		
		while(!queue.isEmpty()) {
			Path path = queue.pop();
			
			if(path.isFuncRet()) {
				retPath = path; continue;
			}
			
			StateExpression state;
			
			if(path == entPath) {
				state = entState;
			} else {
				/* Resolve the phi-node to get the pre-state of join point */
				Map<Path, StateExpression> phiNode = phiNodeTable.row(path);
				StateExpression preState = pathEncoding.noop(phiNode.values());
				phiNode.clear();
				Pair<StateExpression, Boolean> pathStatePair = encodePathWithPreState(path, preState);
				if(!pathStatePair.snd())	return Triple.of(null, null, false);
				state = pathStatePair.fst();
			}
			
			if(path.isFuncEnt() && path != entPath) { // nested function call
				Triple<Path, StateExpression, Boolean> resFuncTriple = 
						statePropagateFuncDFS(graph, path, state, currIterTimesMap);
				if(!resFuncTriple.thd()) return Triple.of(null, null, false);
				
				path = resFuncTriple.fst(); // path is the function return path
				state = resFuncTriple.snd();
			}
    	
      /* find all the successors of path */
			Collection<Path> succs = getSuccessorsViaUnroll(graph, path, currIterTimesMap);
			
			for(Path succ : succs) {
	    	phiNodeTable.put(succ, path, state);
	    	
				int preExprSize = phiNodeTable.row(succ).size();
				int predecessorSize = getCompleteSize(graph, succ, currIterTimesMap);
				
				/* Do not encode the path until all its predecessors are encoded 
				 * note that the graph is acyclic in merged encode 
				 */
				if(preExprSize == predecessorSize) queue.push(succ);
	    }
		}
		
		assert(retPath != null);
		
		/* Resolve the phi-node to get the pre-state of join point */
		Map<Path, StateExpression> phiNode = phiNodeTable.row(retPath);
		StateExpression preState = pathEncoding.noop(phiNode.values());
		phiNode.clear();
		Pair<StateExpression, Boolean> pathStatePair = encodePathWithPreState(retPath, preState);
		return Triple.of(retPath, pathStatePair.fst(), pathStatePair.snd());
	}

  private void preprocessDFS(PreProcessor<?> preprocessor, PathGraph graph, 
  		ImmutableMap<Path, Integer> iterTimesMap) {
  	Preconditions.checkArgument(graph.isValid());
  	
  	Multimap<Path, Path> phiNodeMap = HashMultimap.create();
  	Map<Path, Integer> currIterTimesMap = Maps.newHashMap(iterTimesMap);
  	
  	IOUtils.debug().pln("Preprocessing ...");
  	
  	Deque<Path> queue = Queues.newArrayDeque();
  	queue.push(graph.getSrcPath());
			
  	while(!queue.isEmpty()) {
  		Path path = queue.pop();
				
  		if(path.isFuncEnt()) {
  			path = preprocessFuncDFS(preprocessor, graph, path, currIterTimesMap);
  		}
				
  		IOUtils.debug().pln("Preprocess path " + path);
  		
  		/* pre-process the current path */
  		for(IRStatement stmt : path.getStmts()) preprocessor.analysis(stmt);
		    
  		/* clean pre-process phi-node for further collection */
  		phiNodeMap.removeAll(path);
  		
  		/* find all the successors of path */
  		Collection<Path> succs = getSuccessorsViaUnroll(graph, path, currIterTimesMap);
  			
  		for(Path succ : succs) {
  			phiNodeMap.put(succ, path);
  			
  			int completeSize = getCompleteSize(graph, succ, currIterTimesMap);
  			Collection<Path> succPhiNode = phiNodeMap.get(succ);	
  			
  			/* Process the path until all its predecessors are pre-processed */
  			if(succPhiNode.size() == completeSize) queue.push(succ);
  		}
  	}
	}
	
	/**
   * Encode the function graph, return the function return path,
   * the return state, and the last assertion checking result (if
   * <code>false</code>, no need to proceed further checking)
   * 
   * @param graph
   * @param entPath
   * @param preEntState
   * @param currIterTimesMap 
   * @return
   * @throws PathFactoryException
   */
  private Path preprocessFuncDFS(PreProcessor<?> preprocessor,
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
			
			IOUtils.debug().pln("Preprocessing " + path.stmtsToString());
			
			/* pre-process the current path */
	    for(IRStatement stmt : path.getStmts())	preprocessor.analysis(stmt);
	    
			/* clean preprocess phi-node for further collection */
	    phiNodeMap.removeAll(path);
    	
      /* find all the successors of path */
			Collection<Path> succs = getSuccessorsViaUnroll(graph, path, currIterTimesMap);
			
			for(Path succ : succs) {
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

	/**
   * Check the current statement's pre-condition 
   * 
   * @param stmt
   *          the statement to encode
   * @return false if the statement results in an invalid verification condition
   *         or an infeasible path; true otherwise.
   */
  private boolean checkPreCondition(StateExpression preCond, IRStatement stmt) 
      throws PathFactoryException {
  	
    StateExpressionClosure pre = stmt.getPreCondition(pathEncoding.getExpressionEncoder());
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
 
  /** Encode statement stmt, with single pre-condition */
  private StateExpression encodeStatement(IRStatement stmt, StateExpression preCondition) 
      throws PathFactoryException {
    /* Precondition is OK, encode the postcondition. */
    IOUtils.out().println(stmt.getLocation() + " " + stmt); 
    StateExpression  postCond = stmt.getPostCondition(pathEncoding, preCondition);
    if(IOUtils.debugEnabled()) {
      IOUtils.debug().pln("Post-condition: " + postCond).flush();
      if(postCond.hasConstraint()) {
      	 IOUtils.debug().pln("Constraint: " + postCond.getConstraint()).flush();
      }
    }
    return postCond;
  }
  
  /**
   * Encode current path with a collection of pre-conditions
   * 
   * @return a pair of pre-condition and whether the checking 
   * of prover is succeeded or not.
   * 
   * @throws PathFactoryException 
   */
  private Pair<StateExpression, Boolean> encodeEdgePath(Path currPath, StateExpression preState) 
  		throws PathFactoryException {
		Preconditions.checkArgument(currPath.getSize() == 1);
		IRStatement stmt = currPath.getStmt(0);
				
		StateExpression currState = encodeStatement(stmt, preState);
		currState.addGuard(currState.getConstraint());
  	
  	boolean succeed = checkPreCondition(currState, stmt);
    if(!succeed) {
      if (runIsValid() && !runIsFeasible())
        IOUtils.err().println("WARNING: path assumptions are unsatisfiable");
      return Pair.of(currState, succeed);
    }
    return Pair.of(currState, succeed);
  }
  
  private Pair<StateExpression, Boolean> encodeNonEdgePath(Path currPath, StateExpression preState) 
  		throws PathFactoryException {
  	StateExpression currState = preState;
  	boolean succeed = false;
    for(IRStatement stmt : currPath.getStmts()) {  		
    	currState = encodeStatement(stmt, currState);
      
      succeed = checkPreCondition(currState, stmt);
      if(!succeed) {
        if (runIsValid() && !runIsFeasible())
          IOUtils.err().println("WARNING: path assumptions are unsatisfiable");
        return Pair.of(currState, succeed);
      }
    }
    return Pair.of(currState, succeed);
  }
  
  private Pair<StateExpression, Boolean> encodePathWithPreState(Path currPath, StateExpression preState) 
  		throws PathFactoryException {
  	if(currPath.isEmpty()) return Pair.of(preState, true);
  	
  	if(currPath.isEdgePath()) // edge path
  		return encodeEdgePath(currPath, preState);
  	else 
  		return encodeNonEdgePath(currPath, preState);
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
		if(!iterTimesMap.containsKey(succ)) // non-loop entry
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
}
