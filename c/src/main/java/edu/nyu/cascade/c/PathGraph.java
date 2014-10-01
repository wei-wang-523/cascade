package edu.nyu.cascade.c;

import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.Map.Entry;
import java.util.SortedSet;

import xtc.tree.GNode;
import xtc.tree.Node;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableListMultimap;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableMultimap;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Multimaps;
import com.google.common.collect.Queues;
import com.google.common.collect.Sets;

import edu.nyu.cascade.control.Position;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRStatement.StatementType;
import edu.nyu.cascade.ir.impl.IRExpressionImpl;
import edu.nyu.cascade.ir.impl.Statement;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;

/**
 * Path graph whose nodes are path (a collection of statements). It is
 * created for keep the structure of the CFG, but with changes like
 * assertion/assumption injections, function inlining and loop labeling
 * (unrolling is happened in the encoder).
 * 
 * @author Wei
 *
 */
public final class PathGraph {
	
  private final ImmutableMultimap<Path, Path> predecessorMap, successorMap;
  private final Path srcPath, destPath;
  private final SortedSet<Path> pathSet;
  
  private PathGraph(Multimap<Path, Path> map, Path srcPath, Path destPath) {
	  this.destPath = destPath;
	  this.srcPath = srcPath;
	  predecessorMap = ImmutableMultimap.copyOf(map);
	  successorMap = predecessorMap.inverse();
	  pathSet = Sets.newTreeSet();
	  pathSet.add(srcPath);
	  pathSet.addAll(map.keySet());
	}
  
  private PathGraph(Path srcPath) {
	  this.srcPath = srcPath;
	  destPath = srcPath;
	  predecessorMap = ImmutableMultimap.of();
	  successorMap = ImmutableMultimap.of();
	  pathSet = Sets.newTreeSet();
	  pathSet.add(srcPath);
	}

  @Override
	public String toString() {
	  StringBuilder sb = new StringBuilder();
	  sb.append(srcPath).append("-->").append(destPath);
	  return sb.toString();
	}
  
  @Override
  public PathGraph clone() {
  	Map<Path, Path> replacePair = Maps.newHashMapWithExpectedSize(pathSet.size());
  	for(Path path : pathSet) {
  		Path copyPath = path.clone();
  		replacePair.put(path, copyPath);
  	}
  	
  	return PathGraph.replacePath(this, replacePair);
  }

	Path getSrcPath() { return srcPath; }

  Path getDestPath() { return destPath; }
  
  Collection<Path> getPathSet() { return pathSet;}

	Multimap<Path, Path> getPredecessorMap() { return predecessorMap; }
	
	Multimap<Path, Path> getSuccessorMap() { return successorMap; }

	boolean isLoop() {
		return srcPath == destPath && !predecessorMap.isEmpty();
	}

	/**
	 * Check the graph is valid when debug flag is enabled, otherwise, return true
	 * @return
	 */
	boolean isValid() {
		if(!IOUtils.debugEnabled()) return true;
		
		if(predecessorMap.isEmpty()) return(destPath == srcPath);
		
	  Multimap<Path, Path> map = HashMultimap.create(predecessorMap);
	  Deque<Path> queue = Queues.newArrayDeque();
	  Set<Path> visited = Sets.newHashSet();
	  queue.add(destPath);
	  
	  while(!queue.isEmpty()) {
	    Path path = queue.poll();
	    if(visited.contains(path)) continue;
	    
	    visited.add(path);
	    Collection<Path> prePaths = map.removeAll(path);
	    queue.addAll(prePaths);
	  }
	  
	  return map.isEmpty() && visited.contains(srcPath);
	}

	/**
	 * Create a graph with a singleton <code>path</code>
	 * @param path
	 * @return
	 */
	static PathGraph createSingleton(Path path) {
    return new PathGraph(path);
  }
  
	/**
	 * Create a graph with predecessor <code>map</code> and
	 * <code>srcPath</code> and <code>destPath</code>
	 * @param map
	 * @param srcPath
	 * @param destPath
	 * @return
	 */
  static PathGraph create(Multimap<Path, Path> map, 
      Path srcPath, Path destPath) {
    return new PathGraph(map, srcPath, destPath);
  }
	
  /** Connect two graphs <code>preGraph</code>, <code>graph</code> */
  static PathGraph connect(PathGraph preGraph, PathGraph graph) {
    Preconditions.checkArgument(preGraph.isValid());
    Preconditions.checkArgument(graph.isValid());
    
    Multimap<Path, Path> map = graph.getPredecessorMap();
    Multimap<Path, Path> preMap = preGraph.getPredecessorMap();
    
    Multimap<Path, Path> newMap = HashMultimap.create(map);
    newMap.putAll(preMap);
    
    if(preGraph.getDestPath() != graph.getSrcPath()) {
    	newMap.put(graph.getSrcPath(), preGraph.getDestPath());
    }
    
    Path newSrcPath = preGraph.getSrcPath();
    Path newDestPath = graph.getDestPath();
    
    return PathGraph.create(newMap, newSrcPath, newDestPath);
  }
  
	/**
	 * Add <code>path</code> as source path of the <code>graph</code>
	 * @param graph
	 * @param path
	 * @return
	 */
	static PathGraph addPrePath(PathGraph graph, Path path) {
		Preconditions.checkArgument(graph.isValid());
		Preconditions.checkNotNull(path);
		if(path.isEmpty())	return graph;
	  
		Multimap<Path, Path> map = HashMultimap.create(graph.getPredecessorMap());
		Path srcPath = graph.getSrcPath();
		Path destPath = graph.getDestPath();
		map.put(srcPath, path);
	  srcPath = path;
	  return PathGraph.create(map, srcPath, destPath);
	}

	/**
	 * Add <code>path</code> as destination path to the <code>graph</code>
	 * @param graph
	 * @param path
	 * @return
	 */
	static PathGraph addPostPath(PathGraph graph, Path path) {
		Preconditions.checkNotNull(path);
		Preconditions.checkArgument(graph.isValid());
		if(path.isEmpty())	return graph;
	  
		Multimap<Path, Path> map = HashMultimap.create(graph.getPredecessorMap());
		Path srcPath = graph.getSrcPath();
		Path destPath = graph.getDestPath();
		
		if( graph.isLoop() )	{ // loop
	  	for(Path keyPath : map.keySet()) {
	  		if(map.containsEntry(keyPath, destPath)) {
	  			map.remove(keyPath, destPath);
	  			map.put(keyPath, path);
	  		}
	  	}
	  	map.put(path, destPath);
	  } else {
	  	map.put(path, destPath);
	    destPath = path;
	  }
		
		return PathGraph.create(map, srcPath, destPath);
	}

	/** Compress the graph */
	static PathGraph simplify(IRControlFlowGraph cfg, PathGraph graph) {
		PathGraph resGraph = graph;
		
		if(Preferences.isSet(Preferences.OPTION_PATH_BASED))
			resGraph = isolateStatement(cfg, graph, new Predicate<IRStatement>(){
				@Override
				public boolean apply(IRStatement stmt) {
					return StatementType.ASSERT.equals(stmt.getType());
				}
			}); 
		
		resGraph = compressBFS(resGraph);
		return resGraph;
	}

	/**
	 * Merge the graphs in <code>inlineMap</code> into <code>graph</code>
	 * @param graph
	 * @param inlineMap
	 * @return
	 */
	static PathGraph insertInlineMap(PathGraph graph, Map<Path, PathGraph> inlineMap) {
		if(inlineMap.isEmpty()) return graph;
		
    /* Generate a new graph predecessor map */
    Multimap<Path, Path> predecessorMap = HashMultimap.create();
    
    for(Map.Entry<Path, Path> entry : graph.getPredecessorMap().entries()) {
    	Path valuePath = entry.getValue();
    	Path keyPath = entry.getKey();
    	
    	/* Update the key, if it is function call path */
    	if(inlineMap.containsKey(keyPath)) {
    		Path srcPath = inlineMap.get(keyPath).getSrcPath();
    		if(keyPath.isLoopEnter()) srcPath.labelLoopEnter();
    		if(keyPath.isLoopEntry()) assert srcPath.isLoopEntry();
    		keyPath = srcPath;
    	}
    	
    	/* Update the value, if contains function call path */
    	if(inlineMap.containsKey(valuePath)) {
    		Path destPath = inlineMap.get(valuePath).getDestPath();
    		if(keyPath.isLoopBack()) destPath.labelLoopBack();
    		valuePath = destPath;
    	}
    	
    	predecessorMap.put(keyPath, valuePath);
    }
    
    for(Path keyPath : inlineMap.keySet())
      predecessorMap.putAll(inlineMap.get(keyPath).getPredecessorMap());

    Path srcPath = graph.getSrcPath();
    if(inlineMap.containsKey(srcPath)) {
    	Path srcPathPrime = inlineMap.get(srcPath).getSrcPath();
    	srcPath = srcPathPrime;
    }
    	
    Path destPath = graph.getDestPath();
    if(inlineMap.containsKey(destPath)) {
    	Path destPathPrime = inlineMap.get(destPath).getDestPath();
    	destPath = destPathPrime;
    }
      
    return PathGraph.create(predecessorMap, srcPath, destPath);
	}

	/**
	 * Insert argument-parameter assign statements after parameter declarations
	 * @param graph
	 * @param assignStmts
	 * @return
	 */
	static PathGraph insertParamArgAssignStmts(PathGraph graph, Collection<IRStatement> assignStmts) {
		Path srcPath = graph.getSrcPath();
		assert srcPath.isFuncEnt();
		
		Collection<Path> succPaths = graph.getSuccessorMap().get(srcPath);
		assert(succPaths.size() == 1);
		Path paramDeclarePath = succPaths.iterator().next();
	  	
		List<IRStatement> stmts = Lists.newArrayList();
		
		Iterator<IRStatement> itr = assignStmts.iterator();
		for(IRStatement stmt : paramDeclarePath.getStmts()) {
			stmts.add(stmt);
			if(StatementType.DECLARE.equals(stmt.getType())) {
				if(itr.hasNext()) stmts.add(itr.next());
			}
		}
	  	
		Path newPath = Path.create(stmts);
		Map<Path, Path> replacePair = Collections.singletonMap(paramDeclarePath, newPath);
		return replacePath(graph, replacePair);
	}

	/** Replace the return statement with assign statement */
	static PathGraph appendReturnStmt(PathGraph graph, IRStatement assignStmt) {
	  Preconditions.checkArgument(assignStmt.getType().equals(StatementType.ASSIGN));
	  Path retPath = graph.getDestPath();
	  assert(retPath.isFuncRet());
	  
	  Map<Path, Path> replacePair = Maps.newHashMap();
	  Collection<Path> preRetPaths = graph.getPredecessorMap().get(retPath);
	  
	  for(Path returnPath : preRetPaths) {
	  	if(returnPath.isEmpty()) continue;
	  	int size = returnPath.getSize();
	  	IRStatement returnStmt = returnPath.getStmt(size - 1);
	  	assert(StatementType.RETURN.equals(returnStmt.getType()));
	  	IRStatement retAsgn = createReturnAssignStmt(returnStmt, assignStmt);
	  	List<IRStatement> stmts = Lists.newArrayList(returnPath.getStmts());
	  	stmts.add(retAsgn);
	  	Path newPath = Path.create(stmts);
      replacePair.put(returnPath, newPath);
	  }
	  
	  return replacePath(graph, replacePair);
	}

	/**
	 * Labeling the entry path of loop <code>graph</code>, add the 
	 * iteration times <code>iterTimes</code> to the entry path
	 * @param graph
	 * @param iterTimes
	 */
	static void labelLoop(PathGraph graph, int iterTimes) {
		Preconditions.checkArgument(graph.isValid());
		Preconditions.checkArgument(graph.isLoop());
		
		Path srcPath = graph.getSrcPath();
		srcPath.labelLoopEntry(iterTimes);
		
		Collection<Path> loopEnterPaths = graph.getSuccessorMap().get(srcPath);
		for(Path loopEnter : loopEnterPaths) {
			loopEnter.labelLoopEnter();
		}
		
		Collection<Path> backPaths = graph.getPredecessorMap().get(srcPath);
		
		for(Path realBack : backPaths) {
			realBack.labelLoopBack();
		}
	}

	/**
	 * Find the loop entry for <code>pos</code>. If there's no loop
	 * entry fits, just return the path with the exact location as
	 * <code>pos</code>
	 * @param pos
	 * @return
	 */
	Path getPathForLoopPos(final Position pos) {
		Preconditions.checkArgument(pos.hasLoop());
		Iterable<Path> targetPaths = Iterables.filter(pathSet, new Predicate<Path>(){
			@Override
			public boolean apply(Path path) {
				IRLocation startLoc = path.getStartLoc();
				IRLocation endLoc = path.getEndLoc();
				if(startLoc == null || endLoc == null) return false;
				return pos.follows(startLoc) && pos.precedes(endLoc);
			}
		});
		
		Path loopPath = Iterables.find(targetPaths, new Predicate<Path>() {
			@Override
			public boolean apply(Path path) {
				return path.isLoopPath();
			}
		}, targetPaths.iterator().next());
		
		return loopPath;
	}

	/**
	 * Get the havoc loop graph, by lifting all havoc statements
	 * @param loopGraph
	 * @param assumeStmt
	 * @param assertStmt
	 * @return
	 */
	static PathGraph getHavocLoop(
			PathGraph loopGraph,
			IRStatement assumeStmt,
			IRStatement assertStmt) {
		Preconditions.checkArgument(loopGraph.isLoop());
		Collection<IRStatement> liftStmts = liftHavocDeclStatements(loopGraph);
	
	  Map<Path, Path> replacePair = Maps.newHashMap();
	  
		Deque<Path> queue = Queues.newArrayDeque();
		Set<Path> visited = Sets.newHashSet();
		queue.add(loopGraph.srcPath);
		
		boolean gotLoopEntry = false;
		
		while(!queue.isEmpty()) {
			Path currPath = queue.poll();
			if(visited.contains(currPath)) continue;
			
			visited.add(currPath);
			queue.addAll(loopGraph.getSuccessorMap().get(currPath));
			
			if(currPath.isLoopEntry()) gotLoopEntry = true;
			
			if(!gotLoopEntry) continue;
			
	    Iterable<IRStatement> stmts = Iterables.filter(currPath.getStmts(),
	    		new Predicate<IRStatement>() {
	    	@Override
	    	public boolean apply(IRStatement stmt) {
	    		return !StatementType.DECLARE.equals(stmt.getType());
	    	}
	    });
	    
	    /* nothing has been filtered out */
	    if(Iterables.size(stmts) == currPath.getSize()) continue;
	    
	    Path currPathPrime = Path.create(stmts);
	    
	    replacePair.put(currPath, currPathPrime);
	  }
	  
	  PathGraph graphPrime = replacePath(loopGraph, replacePair);
	  
	  assert(graphPrime.isValid());
	  
	  List<IRStatement> preStmts = Lists.newArrayList();
	  preStmts.add(assertStmt);
	  preStmts.addAll(liftStmts);
	  preStmts.add(assumeStmt);
	  Path prePath = Path.create(preStmts);
	  
	  List<IRStatement> postStmts = Lists.newArrayList();
	  postStmts.addAll(graphPrime.getDestPath().getStmts());
	  postStmts.add(assertStmt);
	  Path postPath = Path.create(postStmts);
	  
	  prePath.labelInvPreCond();
	  postPath.labelInvPostCond();
	  
	  PathGraph resGraph = addInvPath(graphPrime, prePath, postPath);
	  
	  assert(resGraph.isValid());
	  return resGraph;
	}
	
	/** Collect iteration times for all loop entries in <code>graph</code> */
	static ImmutableMap<Path, Integer> initIterTimesMap(PathGraph graph) {
		ImmutableMap.Builder<Path, Integer> mapBuilder = 
				new ImmutableMap.Builder<Path, Integer>();
		
  	for(Path path : graph.getPathSet()) {
  		if(path.isLoopEntry()) {
  			int iterTimes = path.getIterTimes();
  			if(iterTimes > 0)	mapBuilder.put(path, iterTimes);
  		}
  	}
		return mapBuilder.build();
  }
	
	/** Collect all loop entries in <code>graph</code> and set the iteration
	 * times as <code>iterTimes</code> 
	 */
	static ImmutableMap<Path, Integer> initIterTimesMap(PathGraph graph, int iterTimes) {
		Preconditions.checkArgument(iterTimes >= 0);
		
		ImmutableMap.Builder<Path, Integer> mapBuilder = 
				new ImmutableMap.Builder<Path, Integer>();
		
  	for(Path path : graph.getPathSet()) {
  		if(path.isLoopEntry()) {
  			mapBuilder.put(path, iterTimes);
  		}
  	}
		return mapBuilder.build();
  }
	
	@SuppressWarnings("unchecked")
	/**
	 * Collect the loop initiation, enter, back and exit map for every
	 * loop entry path in <code>graph</code>
	 * 
	 * @param graph
	 * @return
	 */
  static List<Multimap<Path, Path>> getLoopInfo(PathGraph graph) {
		
		Multimap<Path, Path> loopInitMap = HashMultimap.create();
		Multimap<Path, Path> loopEnterMap = HashMultimap.create();
	  Multimap<Path, Path> loopBackMap = HashMultimap.create();
		Multimap<Path, Path> loopExitMap = HashMultimap.create();
	  
		for(Path path : graph.getPathSet()) {
			if(!path.isLoopEntry()) continue;
	
			for(Path incomingPath : graph.getPredecessorMap().get(path)) {
				if(incomingPath.isLoopBack()) {
					loopBackMap.put(path, incomingPath);
				} else {
					loopInitMap.put(path, incomingPath);
				}
			}
				
			for(Path outgoingPath : graph.getSuccessorMap().get(path)) {
				if(outgoingPath.isLoopEnter()) {
					loopEnterMap.put(path, outgoingPath);
				} else {
					loopExitMap.put(path, outgoingPath);
				}
			}
		}
		return Lists.newArrayList(loopInitMap, loopEnterMap, loopBackMap, loopExitMap);
	}

	/**
	 * Lift the local declarations inside loop body, used for path-based encoding
	 * @param graph
	 * @return
	 */
	static PathGraph liftLocalDeclaration(PathGraph graph) {
		List<Multimap<Path, Path>> loopRoadMap = getLoopInfo(graph);
		Multimap<Path, Path> loopInitMap = loopRoadMap.get(0);
		Multimap<Path, Path> loopEnterMap = loopRoadMap.get(1);
	  Multimap<Path, Path> loopBackMap = loopRoadMap.get(2);
		Multimap<Path, Path> loopExitMap = loopRoadMap.get(3);
		
		Map<Path, Path> replaceMap = Maps.newHashMap();
		Map<Path, List<Path>> liftPathMap = Maps.newHashMap();
		
		Deque<Path> loopEntryStack = Queues.newArrayDeque();
		Multimap<Path, Path> phiNodeMap = HashMultimap.create();
		Deque<Path> queue = Queues.newArrayDeque();
		queue.add(graph.getSrcPath());
		
		/* Collect lifted paths for top-level the loop entry in the liftPathMap.
		 * Collect replace pair of the original path and the declaration clean 
		 * path in the replaceMap.
	   */
		
		{
			List<Path> liftPaths = Lists.newArrayList(); 
			
			while(!queue.isEmpty()) {
				Path currPath = queue.pop();
				Collection<Path> succs;
				
				/* Clean phi node for further collection, for loop entry path in 
				 * particular. The first time, store <loop entry, loop init>. 
				 * Clean it to collect <loop entry, loop back>.
				 */
				phiNodeMap.removeAll(currPath);
				
				if(currPath.isLoopEntry() && currPath.getIterTimes() > 0) {
					/* If loop entry is visited, get the loop back path,
					 * otherwise, get the loop enter path.
					 */
					if(loopEntryStack.contains(currPath)) {
						loopEntryStack.pop();
						succs = loopExitMap.get(currPath);
						
						/* Find the right loop entry to insert lift paths,*/
						if(loopEntryStack.isEmpty()) {
							if(!liftPaths.isEmpty())	
								liftPathMap.put(currPath, ImmutableList.copyOf(liftPaths));
							
							liftPaths.clear();
						}
					} else {
						loopEntryStack.push(currPath);
						succs = loopEnterMap.get(currPath);
					}
				} else {
					succs = graph.getSuccessorMap().get(currPath);
					
					/* In loop now, collecting lift paths */
					if(!loopEntryStack.isEmpty()) {
						if(currPath.isFuncEnt() || currPath.isFuncRet()) {
							liftPaths.add(currPath.clone());
						} else {
							int size = currPath.getStmts().size();
							Collection<IRStatement> declStmts, leftStmts; 
							declStmts = Lists.newArrayListWithExpectedSize(size);
							leftStmts = Lists.newArrayListWithExpectedSize(size);
							
							for(IRStatement stmt : currPath.getStmts()) {
								if(StatementType.DECLARE.equals(stmt.getType()))
									declStmts.add(stmt);
								else
									leftStmts.add(stmt);
							}
							
							if(!Iterables.isEmpty(declStmts)) {
								Path declPath = Path.create(declStmts);
								Path leftPath = Path.create(leftStmts);
								liftPaths.add(declPath);
								Path.copyProperties(currPath, leftPath);
								replaceMap.put(currPath, leftPath);
							}
						}
					}
				}
				
				/* Filter the successors */
		    for(Path succ : succs) {
		    	phiNodeMap.put(succ, currPath);
					int visitedPrePathSize = phiNodeMap.get(succ).size();
					int completeSize;
					
					if(!succ.isLoopEntry()) {
						completeSize = graph.getPredecessorMap().get(succ).size();
					} else {
						if(loopEntryStack.contains(succ)) { // visited before
							completeSize = loopBackMap.get(succ).size();
						} else {
							completeSize = loopInitMap.get(succ).size();
						}
					}
					
					/* Do not encode the path until all its predecessors are encoded 
					 * note that the graph is acyclic in merged encode 
					 */
					if(visitedPrePathSize == completeSize) queue.push(succ);
		    }
			}
		}
		
		/* Clean the declaration statement inside loop body */
		
		PathGraph replaceGraph = replacePath(graph, replaceMap);
		
		/* Insert lifted paths */
		
		PathGraph resultGraph;
		
		{
			Multimap<Path, Path> predMap = HashMultimap.create(replaceGraph.getPredecessorMap());
			
			for(Entry<Path, List<Path>> entry : liftPathMap.entrySet()) {
				Path loopEntry = entry.getKey();
				List<Path> insertPaths = entry.getValue();
				
				Path liftHead = insertPaths.get(0);
				Path liftTail = insertPaths.get(insertPaths.size() - 1);
				
				Collection<Path> incomingLoopPaths = predMap.removeAll(loopEntry);
				for(Path incomingPath : incomingLoopPaths) {
					if(incomingPath.isLoopBack()) 
						predMap.put(loopEntry, incomingPath);
					else 
						predMap.put(liftHead, incomingPath);
				}
				
				predMap.put(loopEntry, liftTail);
				
				/* Push the predecessor relation inside lift paths */
				Path prevPath = liftHead;
				for(Path liftedPath : insertPaths) {
					if(liftedPath.equals(prevPath)) continue;
					predMap.put(liftedPath, prevPath);
					prevPath = liftedPath;
				}
			}
			
			resultGraph = PathGraph.create(predMap, replaceGraph.getSrcPath(), replaceGraph.getDestPath());
		}
		
		return resultGraph;
	}
	
	/**
	 * Lift local declaration in loop body in the context sensitive way
	 * @param graph
	 * @return
	 */
	static PathGraph liftLocalDeclarationContextSensitive(PathGraph graph) {
		List<Multimap<Path, Path>> loopRoadMap = getLoopInfo(graph);
		Multimap<Path, Path> loopInitMap = loopRoadMap.get(0);
		Multimap<Path, Path> loopEnterMap = loopRoadMap.get(1);
	  Multimap<Path, Path> loopBackMap = loopRoadMap.get(2);
		Multimap<Path, Path> loopExitMap = loopRoadMap.get(3);
		
		Map<Path, Path> replaceMap = Maps.newHashMap();
		
		/* The map from the top entry and all the lifted paths */
		Map<Path, List<Path>> liftPathMap = Maps.newHashMap();
		
		/* The map from the top loop entry and all the nested loop entries 
		 * requires to be wrap with lift begin and lift end statements 
		 */
		Multimap<Path, Path> nestLoopEntryMap = HashMultimap.create();
		
		Deque<Path> loopEntryStack = Queues.newArrayDeque();
		Multimap<Path, Path> phiNodeMap = HashMultimap.create();
		Queue<Path> queue = Queues.newArrayDeque();
		queue.add(graph.getSrcPath());
		
		/* Collect lifted paths for top-level the loop entry in the liftPathMap.
		 * Collect replace pair of the original path and the declaration clean 
		 * path in the replaceMap. Collect the nested loop entries needs to be
		 * wrap with lift begin and lift end paths
	   */
		{
			List<Path> liftPaths = Lists.newArrayList();
			
			while(!queue.isEmpty()) {
				Path currPath = queue.poll();
				Collection<Path> succs;
				
				/* Clean phi node for further collection, for loop entry path in 
				 * particular. Before loop unrolling, store <loop entry, loop init>;
				 * after loop unrolling, clean it to collect <loop entry, loop back>.
				 */
				phiNodeMap.removeAll(currPath);
				
				if(currPath.isLoopEntry() && currPath.getIterTimes() > 0) {
					/* If loop entry is visited, get the loop back path,
					 * otherwise, get the loop enter path.
					 */
					if(loopEntryStack.contains(currPath)) {
						loopEntryStack.pop();
						succs = loopExitMap.get(currPath);
						
						/* Find the right loop entry to insert lift paths,*/
						if(loopEntryStack.isEmpty()) {
							if(!liftPaths.isEmpty()) {
								liftPathMap.put(currPath, Lists.newArrayList(liftPaths));
								nestLoopEntryMap.put(currPath, currPath);
							}
							liftPaths.clear();
						}
					} else {
						loopEntryStack.push(currPath);
						succs = loopEnterMap.get(currPath);
					}
				} else {
					succs = graph.getSuccessorMap().get(currPath);
					
					/* In loop now, collecting lift paths */
					if(!loopEntryStack.isEmpty()) {
						if(currPath.isFuncEnt() || currPath.isFuncRet()) {
							liftPaths.add(currPath.clone());
							nestLoopEntryMap.put(loopEntryStack.peekLast(), loopEntryStack.peek());
						} else {
							ImmutableListMultimap<Boolean, IRStatement> partitionedMap = 
									Multimaps.index(currPath.getStmts(), new Function<IRStatement, Boolean>(){
								@Override
								public Boolean apply(IRStatement stmt) {
									return StatementType.DECLARE.equals(stmt.getType());
								}
							});
							
							if(!partitionedMap.get(true).isEmpty()) {
								Path declPath = Path.create(partitionedMap.get(true));
								Path leftPath = Path.create(partitionedMap.get(false));
								replaceMap.put(currPath, leftPath); // clear declaration statements
								Path.copyProperties(currPath, leftPath);
								liftPaths.add(declPath);
								nestLoopEntryMap.put(loopEntryStack.peekLast(), loopEntryStack.peek());
							}
						}
					}
				}
				
				/* Filter the successors */
		    for(Path succ : succs) {
		    	phiNodeMap.put(succ, currPath);
					int visitedPrePathSize = phiNodeMap.get(succ).size();
					int completeSize;
					
					if(!succ.isLoopEntry()) {
						completeSize = graph.getPredecessorMap().get(succ).size();
					} else {
						if(loopEntryStack.contains(succ)) { // visited before
							completeSize = loopBackMap.get(succ).size();
						} else {
							completeSize = loopInitMap.get(succ).size();
						}
					}
					
					/* Do not encode the path until all its predecessors are encoded 
					 * note that the graph is acyclic in merged encode 
					 */
					if(visitedPrePathSize == completeSize) queue.add(succ);
		    }
			}
		}
		
		/* Clean the declaration statement inside loop body */
		PathGraph replaceGraph = replacePath(graph, replaceMap);
		
		Multimap<Path, Path> predMap = HashMultimap.create(replaceGraph.getPredecessorMap());
		
		for(Entry<Path, List<Path>> entry : liftPathMap.entrySet()) {
			Path loopEntry = entry.getKey();
			List<Path> insertPaths = entry.getValue();
			
			IRStatement liftBeginStmt = Statement.LiftBegin();
			IRStatement liftEndStmt = Statement.LiftEnd();
			Path liftBegin = Path.create(liftBeginStmt);
			Path liftEnd = Path.create(liftEndStmt);
			
			/* Insert the lifted path */
			{				
				insertPaths.add(0, liftBegin);
				insertPaths.add(liftEnd);
				
				Collection<Path> incomingLoopPaths = predMap.removeAll(loopEntry);
				for(Path incomingPath : incomingLoopPaths) {
					if(incomingPath.isLoopBack()) 
						predMap.put(loopEntry, incomingPath);
					else 
						predMap.put(liftBegin, incomingPath);
				}
				
				predMap.put(loopEntry, liftEnd);
				
				/* Push the predecessor relation inside lift paths */
				Path prevPath = liftBegin;
				for(Path liftedPath : insertPaths) {
					if(liftedPath.equals(prevPath)) continue;
					predMap.put(liftedPath, prevPath);
					prevPath = liftedPath;
				}
			}
			
			{ /* Wrap the loop body */
				Collection<Path> nestLoopEntries = nestLoopEntryMap.get(loopEntry);
				for(Path nestLoopEntry : nestLoopEntries) {
					Path liftEndCopy = liftEnd.clone();
					Collection<Path> preds = predMap.get(nestLoopEntry);
					for(Path pred : preds) {
						if(pred.isLoopBack()) {
							Collection<Path> preOfPreds = predMap.removeAll(pred);
							predMap.putAll(liftEndCopy, preOfPreds);
							predMap.put(pred, liftEndCopy);
						}
					}
					
					Path liftBeginCopy = liftBegin.clone();
					Collection<Path> succs = replaceGraph.getSuccessorMap().get(nestLoopEntry);
					for(Path succ : succs) {
						if(succ.isLoopEnter()) {
							for(Path succOfSucc : replaceGraph.getSuccessorMap().get(succ)) {
								predMap.remove(succOfSucc, succ);
								predMap.put(succOfSucc, liftBeginCopy);
							}
							predMap.put(liftBeginCopy, succ);
						}
					}
				}
			}
		}
		
		PathGraph resultGraph = PathGraph.create(predMap, 
				replaceGraph.getSrcPath(), replaceGraph.getDestPath());
		
		return resultGraph;
	}

	/**
	 * Add <code>prePath</code> and <code>postPath</code> to <code>graph</code>
	 * for processing invariant
	 */
  private static PathGraph addInvPath(PathGraph graph, Path prePath, Path postPath) {
  	Preconditions.checkArgument(graph.isValid());
  	Preconditions.checkNotNull(prePath);
  	Preconditions.checkNotNull(postPath);
  	
  	if(graph.isLoop()) {
  		Multimap<Path, Path> origPredMap = graph.getPredecessorMap();
			Multimap<Path, Path> predMap = HashMultimap.create(origPredMap);
			
			Path srcPath = graph.getSrcPath();
			Collection<Path> preds = predMap.removeAll(srcPath);
			predMap.put(srcPath, prePath);
			predMap.putAll(postPath, preds);
			return PathGraph.create(predMap, prePath, postPath);
  	}

  	Deque<Path> queue = Queues.newArrayDeque();
		Set<Path> visited = Sets.newHashSet();
		queue.add(graph.getSrcPath());
		while(!queue.isEmpty()) {
			Path currPath = queue.poll();
			if(visited.contains(currPath)) continue;
			
			visited.add(currPath);
			queue.addAll(graph.getSuccessorMap().get(currPath));
			
			if(currPath.isLoopEntry()) {
				Multimap<Path, Path> origPredMap = graph.getPredecessorMap();
				Multimap<Path, Path> predMap = HashMultimap.create(origPredMap);
				for(Path pred : origPredMap.get(currPath)) {
					if(pred.isLoopBack()) {
						predMap.remove(currPath, pred);
						predMap.put(postPath, pred);
					} else {
						predMap.remove(currPath, pred);
						predMap.put(prePath, pred);
						predMap.put(currPath, prePath);
					}
				}
				
				Path destPathPrime = currPath.equals(graph.getDestPath()) ? postPath :
					graph.getDestPath();
					
				return PathGraph.create(predMap, graph.getSrcPath(), destPathPrime);
			}
		}
    
		throw new IllegalStateException("Add invariant to non-loop graph.");
  }
	
	/** Lift the statements of the loop graph for invariant analysis: 
	 *  1) Generate all the havoc statements for value update;
	 *  2) Lift all the havoc statements (but not the nested invariant havoc statements);
	 *  3) Lift all the declaration statements, scope-ent and scope-exit statements;
	 *  5) The <code>loopGraph</code> structure keeps unchanged.
	 *  
	 * 	@param loopGraph
	 */
	private static Collection<IRStatement> liftHavocDeclStatements(PathGraph loopGraph) {
		Preconditions.checkArgument(loopGraph.isLoop());
		
		Deque<Path> queue = Queues.newArrayDeque();
		Set<Path> visited = Sets.newHashSet();
		queue.add(loopGraph.srcPath);
		
		/* Avoid to have multiple havoc statements for same left-variable */
		Set<GNode> havocGNodeSet = Sets.newHashSet();
		
		boolean gotLoopEntry = false;
		List<IRStatement> liftStmts = Lists.newArrayList();
		
		while(!queue.isEmpty()) {
			Path currPath = queue.poll();
			if(visited.contains(currPath)) continue;
			
			visited.add(currPath);
			queue.addAll(loopGraph.getSuccessorMap().get(currPath));
			
			if(currPath.isLoopEntry()) gotLoopEntry = true;
			
			if(!gotLoopEntry) continue;
			
			for(IRStatement stmt : currPath.getStmts()) {
				switch(stmt.getType()) {
				case ALLOC:
				case ASSIGN:
					/* Pick up havoc statements for any update */
					Statement havocStmt = Statement.havoc(stmt.getSourceNode(), stmt.getOperand(0));
					GNode havocGNode = GNode.cast(stmt.getOperand(0).getSourceNode());
					if(havocGNodeSet.contains(havocGNode)) continue;
					
					havocGNodeSet.add(havocGNode);
					liftStmts.add(havocStmt);
					break;
				case HAVOC: 
					/* Ignore the havoc statement in the nested loop invariant,
					 * avoid duplicated havoc statements. */
					if(!(currPath.isInvPreCond() || currPath.isInvPostCond()))
						liftStmts.add(stmt);
					break; 
				case DECLARE:
					liftStmts.add(stmt); break;
				case FUNC_ENT:
				case FUNC_EXIT:
				case LIFT_BEGIN:
				case LIFT_END:
					throw new IllegalArgumentException("Loop body cannot contain function call for now.");
				default:
					break;
				}
			}
		}
		
		return liftStmts;
	}
	
	/**
	 * Replace the path for its replacement stored in <code>replaceMap</code> 
	 * in the <code>graph</code>
	 * @param graph
	 * @param replaceMap
	 * @return
	 */
	private static PathGraph replacePath(PathGraph graph,
      Map<Path, Path> replaceMap) {
		if(replaceMap.isEmpty())  return graph;
    
    Multimap<Path, Path> map = HashMultimap.create();

    for(Entry<Path, Path> entry : graph.getPredecessorMap().entries()) {
    	
    	// update value if value path is replaced
    	Path valuePath = entry.getValue();
    	if(replaceMap.containsKey(valuePath)) {
    		valuePath = replaceMap.get(valuePath);
    	}
    	
    	// update key if key path is replaced
    	Path keyPath = entry.getKey();
    	if(replaceMap.containsKey(keyPath)) {
    		keyPath = replaceMap.get(keyPath);
    	}

    	map.put(keyPath, valuePath);
    }
    
    Path srcPath = graph.getSrcPath();
    Path srcPathPrime = replaceMap.containsKey(srcPath) ? 
    		replaceMap.get(srcPath) : srcPath;
    
    Path destPath = graph.getDestPath();
    Path destPathPrime = replaceMap.containsKey(destPath) ?
    		replaceMap.get(destPath) : destPath;
    
    return PathGraph.create(map, srcPathPrime, destPathPrime);
  }
  
  /**
	 * Split each path if contains statement with <code>type</code>, and the split
	 * sub-paths have only a singleton statement with <code>type</code>
	 * 
	 * @param cfg
	 * @param graph
	 * @param type
	 */
	private static PathGraph isolateStatement(
			IRControlFlowGraph cfg, 
			PathGraph graph, 
			Predicate<IRStatement> predicate) {
		
		Collection<Path> pathSet = graph.getPathSet();
		
		Multimap<Path, Path> predecessorMap = HashMultimap.create();
		Map<Path, Path> replaceLastSeg = Maps.newHashMap();
		Map<Path, Path> replaceFirstSeg = Maps.newHashMap();
		
		for(Path path : pathSet) {
			if(path.getStmts().size() <= 1) continue;
			
			if(!Iterables.any(path.getStmts(), predicate)) continue;
			
			List<Path> subPaths = path.isolateKeyStatement(cfg, predicate);
			
			/* Add newly generated edge */
			Iterator<Path> pathItr = subPaths.iterator();
			Path prePath = pathItr.next();
			while(pathItr.hasNext()) {
				Path currPath = pathItr.next();
				predecessorMap.put(currPath, prePath);
				prePath = currPath;
			}
			
			Path firstSegment = subPaths.get(0);
			Path lastSegment = subPaths.get(subPaths.size() - 1);
			
			replaceFirstSeg.put(path, firstSegment);
			replaceLastSeg.put(path, lastSegment);
		}
		
		if(replaceFirstSeg.isEmpty() && replaceLastSeg.isEmpty()) return graph;
		
		for(Entry<Path, Path> entry : graph.getPredecessorMap().entries()) {
			Path key = entry.getKey();
			Path value = entry.getValue();
			
			Path replaceKey = replaceFirstSeg.containsKey(key) ? replaceFirstSeg.get(key) : key;
			Path replaceValue = replaceLastSeg.containsKey(value) ? replaceLastSeg.get(value) : value;
			
			predecessorMap.put(replaceKey, replaceValue);
		}
		
		Path srcPath = graph.getSrcPath();
		Path replaceSrcPath = replaceFirstSeg.containsKey(srcPath) ? 
				replaceFirstSeg.get(srcPath) 
				: srcPath;
		
		Path destPath = graph.getDestPath();
		Path replaceDestPath = replaceLastSeg.containsKey(destPath) ? 
				replaceLastSeg.get(destPath) 
				: destPath;
		
		PathGraph resGraph = PathGraph.create(predecessorMap, replaceSrcPath, replaceDestPath);
		return resGraph;
	}

	/**
	 * Replace the <code>returnStmt</code> as <code>assignStmt</code>
	 * @param returnStmt
	 * @param assignStmt
	 * @return
	 */
  private static IRStatement createReturnAssignStmt(
  		IRStatement returnStmt, 
  		IRStatement assignStmt) {
    Preconditions.checkArgument(StatementType.RETURN.equals(returnStmt.getType()));
    Preconditions.checkArgument(StatementType.ASSIGN.equals(assignStmt.getType()));
    IRExpressionImpl lExpr = (IRExpressionImpl) assignStmt.getOperand(0);
    IRExpressionImpl rExpr = (IRExpressionImpl) returnStmt.getOperand(0);
    Node assignNode = GNode.create("AssignmentExpression", 
        lExpr.getSourceNode(), "=", rExpr.getSourceNode());
    assignNode.setLocation(assignStmt.getSourceNode().getLocation());
    IRStatement assignResult = Statement.assign(assignNode, lExpr, rExpr);
    return assignResult;
  }
  
  /**
   * Simplify graph by merge path to its single predecessor without label
   * @param graph
   * @return
   */
  private static PathGraph compressBFS(PathGraph graph) {
  	final Multimap<Path, Path> predecessorMap = HashMultimap.create(graph.getPredecessorMap());
  	Path srcPath = graph.getSrcPath();
  	
    Deque<Path> queue = Queues.newArrayDeque();
    queue.add(graph.getDestPath());
    
    Map<Path, Path> replacePair = Maps.newHashMap();
    Set<Path> visited = Sets.newHashSet();
    
    /* It's okay to merge prePath with currPath, unless there's
     * no multiple prePaths behind, currPath and prePath have 
     * condition assumption label, that's to keep edge path clean.
     */
    Predicate<Path> readyToMergeUp = new Predicate<Path>(){
			@Override
      public boolean apply(Path path) {
	      if(predecessorMap.get(path).size() > 1) return false;
	      
	      if(path.hasLabel()) return false;
	      
	      return true;
      }
	  };
	  
    Predicate<Path> readyToBeMerged = new Predicate<Path>(){
			@Override
      public boolean apply(Path path) {		      
	      return !path.hasLabel();
      }
	  };
    
    while(!queue.isEmpty()) {
      Path path = queue.poll();
      if(visited.contains(path)) continue; // skip visited
      
      Path currPath = path;
      Collection<Path> prePaths = predecessorMap.get(currPath);
      
      if(!readyToMergeUp.apply(path)) {     
      	queue.addAll(prePaths);
      	visited.add(path);
      	continue;
      }
      
      boolean isMerged = false;
      while(prePaths.size() == 1) {
        Path prePath = prePaths.iterator().next();
        
        if(!readyToBeMerged.apply(prePath)) break;
        
        currPath = Path.mergePath(prePath, currPath); 
        isMerged = true;
        
        prePaths = predecessorMap.removeAll(prePath);
        
        visited.add(prePath);
        
        if(prePath == srcPath)  srcPath = currPath;
      }
      
      queue.addAll(prePaths);
      visited.add(path);
      
      if(isMerged) { // Merge happened
      	replacePair.put(path, currPath);
        predecessorMap.removeAll(path);
        predecessorMap.putAll(currPath, prePaths);
      }
    }
    
    if(replacePair.isEmpty())
    	return graph; // nothing needs to be replaced
    
    /* Iterate map to replace value*/
    Multimap<Path, Path> newMap = HashMultimap.create();
    for(Entry<Path, Path> entry : predecessorMap.entries()) {
    	Path keyPath = entry.getKey();
    	Path valuePath = entry.getValue();
    	
    	if(replacePair.containsKey(valuePath)) {
    		newMap.put(keyPath, replacePair.get(valuePath));
    	} else {
    		newMap.put(keyPath, valuePath);
    	}
    }
    
    Path destPath = graph.getDestPath();
    if(replacePair.containsKey(destPath))
      destPath = replacePair.get(destPath);
    
    return PathGraph.create(newMap, srcPath, destPath);
  }
}
