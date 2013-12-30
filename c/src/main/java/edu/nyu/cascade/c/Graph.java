package edu.nyu.cascade.c;

import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.Map.Entry;

import xtc.tree.GNode;
import xtc.tree.Node;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRStatement.StatementType;
import edu.nyu.cascade.ir.impl.IRExpressionImpl;
import edu.nyu.cascade.ir.impl.Statement;

public final class Graph {
  final static String COND_ASSUME_LABEL = "COND_ASSUME";
  private Map<Path, Set<Path>> predecessorMap = null;
  private Path srcPath = null;
  private Path destPath = null;
  
  public Path getSrcPath() {
		return srcPath;
	}

	public Path getDestPath() {
		return destPath;
	}

	static Graph createSingleton(Path path) {
    Map<Path, Set<Path>> emptyMap = Maps.newLinkedHashMap();
    return new Graph(emptyMap, path, path);
  }
  
  static Graph create(Map<Path, Set<Path>> map, 
      Path srcPath, Path destPath) {
  	Preconditions.checkArgument(isValid(destPath, srcPath, map));
    return new Graph(map, srcPath, destPath);
  }
  
  private Graph(Map<Path, Set<Path>> map, Path srcPath, Path destPath) {
    //FIXME: destPath = destPath.copy() ?
    this.destPath = destPath;
    this.srcPath = srcPath;
    this.predecessorMap = map;
  }
  
  void setDestPath(Path destPath) {
    this.destPath = destPath;
  }
  
  void setSrcPath(Path srcPath) {
    this.srcPath = srcPath;
  }
  
  boolean hasNullMap() {
  	return predecessorMap == null;
  }
  
  Map<Path, Set<Path>> getPredecessorMap() {
  	return predecessorMap;
  }
  
  IRBasicBlock getDestBlock() {
    if(destPath == null)    return null;
    return destPath.getDestBlock();
  }
  
  IRBasicBlock getSrcBlock() {
    if(srcPath == null)     return null;
    return srcPath.getSrcBlock();
  }
  
  IRStatement getLastStmt() {
    Path currPath = destPath;
    while(currPath.isEmpty()) {      
      if(!predecessorMap.containsKey(currPath)) return null;
      
      Set<Path> prePaths = predecessorMap.get(currPath);
      if(prePaths.size() > 1)   return null;      
      currPath = prePaths.iterator().next();
    }    
    return currPath.getLastStmt();
  }
  
  void appendPreGraph(Graph preGraph) throws RunProcessorException { 
    if(preGraph == null)    return;
    Preconditions.checkArgument(!isConnected(preGraph));
    Preconditions.checkArgument(preGraph.isValid());
    Map<Path, Set<Path>> preMap = preGraph.predecessorMap;
    Path preDestPath = preGraph.destPath;
  
    predecessorMap.putAll(preMap);
    if(preDestPath != srcPath) {
      Set<Path> predecessorPaths = Sets.newHashSet(preDestPath);
    	if(predecessorMap.containsKey(srcPath)) // loop in graph
    		predecessorPaths.addAll(predecessorMap.get(srcPath));
      predecessorMap.put(srcPath, predecessorPaths);
      srcPath = preGraph.srcPath;
    } else {
      srcPath = preGraph.srcPath;
    }
  }
  
  void appendAllPreGraph(Iterable<Graph> preGraphs) throws RunProcessorException { 
    Preconditions.checkNotNull(preGraphs);
    Preconditions.checkArgument(!Iterables.isEmpty(preGraphs));
    Preconditions.checkArgument(Iterables.all(preGraphs, new Predicate<Graph>(){
    	@Override
    	public boolean apply(Graph graph) {
    		return !isConnected(graph) && graph.isValid();
    	}
    }));
    final Path preSrcPath = Iterables.get(preGraphs, 0).srcPath;
    Preconditions.checkArgument(Iterables.all(preGraphs, new Predicate<Graph>(){
      @Override
      public boolean apply(Graph graph) {
        return graph.srcPath==preSrcPath;
      }
    }));
    
    for(Graph preGraph : preGraphs) {
      for(Entry<Path, Set<Path>> entry: preGraph.predecessorMap.entrySet()) {
        Path keyPath = entry.getKey();
        Set<Path> prePaths = entry.getValue();
        if(predecessorMap.containsKey(keyPath))
          prePaths.addAll(predecessorMap.get(keyPath));
        predecessorMap.put(keyPath, prePaths);
      }
    }
    
    Iterable<Path> preDestPaths = Iterables.transform(preGraphs, new Function<Graph, Path>(){
      @Override
      public Path apply(Graph graph) {
        return graph.destPath;
      }
    });
    
    predecessorMap.put(srcPath, Sets.newHashSet(preDestPaths)); 
    srcPath = preSrcPath;
  }
  
  void appendPostGraph(Graph postGraph) throws RunProcessorException {
    if(postGraph == null)   return;
  	Preconditions.checkArgument(postGraph.isValid());
    Preconditions.checkArgument(!isConnected(postGraph));
    Map<Path, Set<Path>> postMap = postGraph.predecessorMap;
    Path postSrcPath = postGraph.srcPath;
    
    predecessorMap.putAll(postMap);
    if(postSrcPath != destPath) {
    	Set<Path> predecessorPaths = Sets.newHashSet(destPath);
    	if(predecessorMap.containsKey(postSrcPath)) // loop in postGraph
    		predecessorPaths.addAll(predecessorMap.get(postSrcPath));
      predecessorMap.put(postSrcPath, predecessorPaths); 
      destPath = postGraph.destPath;
    } else {
      destPath = postGraph.destPath;
    }
  }
  
  void addInvariantPath(Path prePath, Path postPath) throws RunProcessorException {
  	Preconditions.checkArgument(isValid());
    if(prePath == null || postPath == null)    return;
    assert(srcPath.isCopyOf(destPath));
    Set<Path> preDestPaths = predecessorMap.remove(destPath);
    predecessorMap.put(postPath, preDestPaths);
    predecessorMap.put(srcPath, Sets.newHashSet(prePath));
    srcPath = prePath;
    destPath = postPath;
  }
  
  void insertBefore(Path destPath, Path insertPath) 
  		throws RunProcessorException {
    Preconditions.checkArgument(destPath != null);
    if(insertPath == null)  return;
    Set<Path> prePaths = predecessorMap.remove(destPath);
    predecessorMap.put(destPath, Sets.newHashSet(insertPath));
    if(prePaths != null) {
      predecessorMap.put(insertPath, prePaths);
    } else {
      assert(this.srcPath == this.destPath);
      srcPath = insertPath;
    }
  }
  
  void appendPrePath(Path path) throws RunProcessorException {
  	Preconditions.checkArgument(isValid());
    if(path == null)    return;
    if( isLoop() )	{ // loop
    	Set<Path> preSrcPath = predecessorMap.remove(srcPath);
    	predecessorMap.put(path, preSrcPath);
    	predecessorMap.put(srcPath, Sets.newHashSet(path));
    } else {
    	Preconditions.checkArgument(!predecessorMap.containsKey(srcPath));
      predecessorMap.put(srcPath, Sets.newHashSet(path));
      srcPath = path;
    }
  }
  
  void appendPostPath(Path path) throws RunProcessorException {
    if(path == null)    return;
    Preconditions.checkArgument(isValid());
    if( isLoop() )	{ // loop
    	Set<Path> keySet = predecessorMap.keySet();
    	for(Path keyPath : keySet) {
    		Set<Path> prePaths = predecessorMap.get(keyPath);
    		if(prePaths.contains(destPath)) {
    			prePaths.remove(destPath);
    			prePaths.add(path);
    			predecessorMap.put(keyPath, prePaths);
    		}
    	}
      predecessorMap.put(path, Sets.newHashSet(destPath));
    } else {
      predecessorMap.put(path, Sets.newHashSet(destPath));
      destPath = path;
    }
  }
  
  boolean isLoop() {
  	return srcPath == destPath && !predecessorMap.isEmpty();
  }
  
  private boolean isConnected(Graph graph) {
  	Set<Path> keyPaths1 = predecessorMap.keySet();
  	Set<Path> keyPaths2 = graph.predecessorMap.keySet();
  	for(Path keyPath1 : keyPaths1) {
  		if(keyPaths2.contains(keyPath1)) return true;
  	}
  	return false;
  }
  
  private boolean hasReturnStmt(Path path) {
    if(path == null || path.isEmpty())  {
      Set<Path> prePaths = predecessorMap.get(path);
      Path prePath = prePaths.iterator().next();
      return hasReturnStmt(prePath);
    } else {
      IRStatement stmt = path.getStmts().get(path.getStmts().size()-1);
      return stmt.getType().equals(IRStatement.StatementType.RETURN);
    }
  }
  
  boolean hasReturnStmt() {
    return hasReturnStmt(destPath);
  }
  
  private IRStatement getReturnStmt(Path path) {
    if(path == null || path.isEmpty())  {
      Set<Path> prePaths = predecessorMap.get(path);
      Path prePath = prePaths.iterator().next();
      return getReturnStmt(prePath);
    } else {
      IRStatement stmt = path.getStmts().get(path.getStmts().size()-1);
      return stmt;
    }
  }
  
  IRStatement getReturnStmt() {
    Preconditions.checkArgument(hasReturnStmt());
    return getReturnStmt(destPath);
  }
  
  /** Replace the last return statement as assign statement. */
  private IRStatement replaceReturnStmt(IRStatement returnStmt, IRStatement assignStmt) {
    Preconditions.checkArgument(returnStmt.getType().equals(StatementType.RETURN));
    IRExpressionImpl lExpr = (IRExpressionImpl) assignStmt.getOperand(0);
    IRExpressionImpl rExpr = (IRExpressionImpl) returnStmt.getOperand(0);
    Node assignNode = GNode.create("AssignmentExpression", 
        lExpr.getSourceNode(), "=", rExpr.getSourceNode());
    assignNode.setLocation(assignStmt.getSourceNode().getLocation());
    IRStatement assignResult = Statement.assign(assignNode, lExpr, rExpr);
    return assignResult;
  }
  
  /**
   * Replace the return statement with assign statement, return true if replace
   * actually happened
   */
  public boolean replaceReturnStmt(IRStatement assignStmt) {
    Preconditions.checkArgument(assignStmt.getType().equals(StatementType.ASSIGN));
    Queue<Path> queue = Lists.newLinkedList();
    queue.add(destPath);
    Map<Path, Set<Path>> successorMap = Maps.newHashMap();
    while(!queue.isEmpty()) {
      Path currPath = queue.poll();
      if(currPath.isEmpty()) {
      	Set<Path> prePaths =  predecessorMap.get(currPath);
      	if(prePaths == null)	continue;
        for(Path prePath : prePaths) {
          queue.add(prePath);
          Set<Path> succPaths = null;
          if(successorMap.containsKey(prePath))
            succPaths = successorMap.get(prePath);
          else
            succPaths = Sets.newHashSet();
          succPaths.add(currPath);
          successorMap.put(prePath, succPaths);
        }
      } else {
        IRStatement lastStmt = currPath.getLastStmt();
        if(lastStmt.getType().equals(StatementType.RETURN)) {
          IRStatement assignResult = replaceReturnStmt(lastStmt, assignStmt);
          Path newPath = Path.createSingleton(assignResult);
          predecessorMap.put(newPath, Sets.newHashSet(currPath));
//          if(currPath == destPath)	
//          	destPath = newPath;
          Set<Path> succPaths = successorMap.get(currPath);
          if(succPaths == null)	continue;
          for(Path succPath : succPaths) {
            Set<Path> prePaths = predecessorMap.get(succPath);
            prePaths.remove(currPath);
            prePaths.add(newPath);
            predecessorMap.put(succPath, prePaths);
          }
        } else {
          return false;
        }
      }
    }
    return true;
  }
  
  private Path simplify_DFS(Path path, Map<Path, Path> replaceMap) throws RunProcessorException {
    if(replaceMap.containsKey(path)) 
      return replaceMap.get(path);
    Set<Path> prePaths = predecessorMap.get(path);
    if(prePaths == null)    return path;
    
    Set<Path> simplifyPaths = Sets.newHashSet();
    for(Path prePath : prePaths)    
      simplifyPaths.add(simplify_DFS(prePath, replaceMap));
    assert(simplifyPaths.size() >= 1);
    if(simplifyPaths.size() > 1) { 
      predecessorMap.put(path, simplifyPaths);
      return path;
    } else {
      // Path with first statement is conditional assume statement
      if(path.getStmts().size() > 0 && 
          path.getStmts().get(0).getPreLabels().contains(COND_ASSUME_LABEL)) {
        predecessorMap.put(path, simplifyPaths);
        return path;
      } else {
        Path simplifyPath = simplifyPaths.iterator().next();
        Path pathPrime = Path.mergePath(simplifyPath, path);
        assert(!pathPrime.equals(path));
        predecessorMap.remove(path);
        if(predecessorMap.containsKey(simplifyPath)) {
          Set<Path> prePathsPrime = predecessorMap.remove(simplifyPath);
          predecessorMap.put(pathPrime, prePathsPrime);
        }
        if(simplifyPath.equals(srcPath)) srcPath = pathPrime;
        replaceMap.put(path, pathPrime);
        return pathPrime;
      }
    }
  }
  
  void simplify_DFS() throws RunProcessorException {
    Map<Path, Path> replaceMap = Maps.newHashMap();
    destPath = simplify_DFS(destPath, replaceMap);
  }
  
  private void simplify_BFS() throws RunProcessorException {
    Queue<Path> queue = Lists.newLinkedList();
    queue.add(destPath);
    Map<Path, Path> replaceMap = Maps.newHashMap();
    Set<Path> visited = Sets.newHashSet();
    while(!queue.isEmpty()) {
      Path topPath = queue.poll();
      if(visited.contains(topPath)) continue; // skip visited
      
      Path currPath = topPath;
      Set<Path> prePaths = predecessorMap.get(currPath);
      /* It's okay to merge prePath with currPath */
      while(prePaths != null && prePaths.size() == 1 && (currPath.getStmts().size() == 0 || 
          !currPath.getStmts().get(0).getPreLabels().contains(COND_ASSUME_LABEL))) {
        Path prePath = prePaths.iterator().next();
        currPath = Path.mergePath(prePath, currPath);  
        prePaths = predecessorMap.remove(prePath);
        visited.add(prePath);
        if(prePath == srcPath)  srcPath = currPath;
      }
      
      if(topPath != currPath) { // Merge happens
        replaceMap.put(topPath, currPath);
        predecessorMap.remove(topPath);
        if(prePaths != null)
          predecessorMap.put(currPath, prePaths);
      }
      
      if(prePaths != null)      queue.addAll(prePaths);
      visited.add(topPath);
    }
    
    if(replaceMap.isEmpty())    return;
    
    /* Iterate predecessor map */
    Map<Path, Set<Path>> predecessorMapPrime = Maps.newHashMap();
    for(Entry<Path, Set<Path>> entry : predecessorMap.entrySet()) {
      Set<Path> valuePrime = Sets.newHashSet();
      for(Path prePath : entry.getValue()) {
        if(replaceMap.containsKey(prePath))
          valuePrime.add(replaceMap.get(prePath));
        else
          valuePrime.add(prePath);
      }
      predecessorMapPrime.put(entry.getKey(), valuePrime);
    }
    
    predecessorMap = predecessorMapPrime;    
    if(replaceMap.containsKey(destPath))
      destPath = replaceMap.get(destPath);
  }
  
  /** Simplify the graph */
  void simplify() throws RunProcessorException {
//    long startTime = System.currentTimeMillis();
//    simplify_DFS();
    simplify_BFS();
//    double time = (System.currentTimeMillis() - startTime)/1000.0;
//    IOUtils.err().println("Simplify takes time: " + time);
  }
  
  /** find all havoc statement */
  Iterable<IRStatement> collectHavocStmts() {
    Queue<Path> queue = Lists.newLinkedList();
    List<Path> visited = Lists.newArrayList();
    List<IRStatement> resStmts = Lists.newArrayList();
    queue.add(destPath);
    while(!queue.isEmpty()) {
      Path currPath = queue.poll();
      if(visited.contains(currPath))    continue;
      Iterable<IRStatement> assignStmts = Iterables.filter(currPath.getStmts(), 
      		new Predicate<IRStatement>(){
      	@Override
				public boolean apply(IRStatement stmt) {
      		return stmt.getType().equals(StatementType.ASSIGN);
      	}
      });
      
      Iterable<IRStatement> havocStmts = Iterables.transform(assignStmts, 
      		new Function<IRStatement, IRStatement>(){
      	@Override
      	public IRStatement apply(IRStatement stmt) {
      		IRExpressionImpl lval = (IRExpressionImpl) stmt.getOperand(0);
          return Statement.havoc(lval.getSourceNode(), lval);
      	}
      });
      
      resStmts.addAll(0, Lists.newArrayList(havocStmts));
      
      if(predecessorMap.containsKey(currPath))
        queue.addAll(predecessorMap.get(currPath));
      visited.add(currPath);
    }
    return resStmts;
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append(srcPath).append("-->").append(destPath);
    return sb.toString();
  }
  
  boolean isValid() {
  	if(predecessorMap.isEmpty()) {
  		if(destPath == srcPath) return true;
  		return false;
  	}
  	
    Map<Path, Set<Path>> map = Maps.newLinkedHashMap(predecessorMap);
    Queue<Path> queue = Lists.newLinkedList();
    Set<Path> visited = Sets.newHashSet();
    queue.add(destPath);
    visited.add(destPath);
    
    while(!queue.isEmpty()) {
      Path path = queue.poll();
      Set<Path> prePaths = map.remove(path);
      if(prePaths == null) continue;
      for(Path prePath : prePaths) {
        if(!visited.contains(prePath)) {
          queue.add(prePath);
          visited.add(prePath);
        }
      }
    }
    
    return map.isEmpty() && visited.contains(srcPath);
  }
  
  boolean containsLoop() {
  	List<Path> stack = Lists.newArrayList();
   	Set<Path> visited = Sets.newHashSet();
   	stack.add(destPath);
  	while(!stack.isEmpty()) {
  		Path path = stack.remove(0);
  		if(!visited.contains(path)) {
  			visited.add(path);
  			Set<Path> prePaths = predecessorMap.get(path);
  			if(prePaths != null) stack.addAll(prePaths);
  		} else {
  			return true;
  		}
  	}
  	return false;
  }
  
  static boolean isValid(Path _destPath, Path _srcPath, Map<Path, Set<Path>> _predecessorMap) {
  	if(_predecessorMap.isEmpty()) {
  		if(_destPath == _srcPath) return true;
  		return false;
  	}
  	
    Map<Path, Set<Path>> map = Maps.newLinkedHashMap(_predecessorMap);
    Queue<Path> queue = Lists.newLinkedList();
    Set<Path> visited = Sets.newHashSet();
    queue.add(_destPath);
    visited.add(_destPath);
    
    while(!queue.isEmpty()) {
      Path path = queue.poll();
      Set<Path> prePaths = map.remove(path);
      if(prePaths == null) continue;
      for(Path prePath : prePaths) {
        if(!queue.contains(prePath)) {
          queue.add(prePath);
          visited.addAll(prePaths);
        }
      }
    }
    
    return map.isEmpty() && visited.contains(_srcPath);
  }
}
