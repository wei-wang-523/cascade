package edu.nyu.cascade.c;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;

import xtc.parser.ParseException;
import xtc.parser.Result;
import xtc.tree.GNode;
import xtc.tree.Location;
import xtc.tree.Node;
import xtc.type.NumberT;
import xtc.util.Pair;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CAnalyzer;
import edu.nyu.cascade.control.CallPoint;
import edu.nyu.cascade.control.LoopPoint;
import edu.nyu.cascade.control.Position;
import edu.nyu.cascade.control.Run;
import edu.nyu.cascade.control.jaxb.InsertionType;
import edu.nyu.cascade.control.jaxb.Position.Command;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.ir.IRStatement.StatementType;
import edu.nyu.cascade.ir.expr.ExpressionClosure;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.PathEncoding;
import edu.nyu.cascade.ir.expr.PathFactoryException;
import edu.nyu.cascade.ir.expr.SimplePathEncoding;
import edu.nyu.cascade.ir.impl.IRExpressionImpl;
import edu.nyu.cascade.ir.impl.Statement;
import edu.nyu.cascade.ir.impl.VarInfo;
import edu.nyu.cascade.ir.type.IRIntegerType;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.c.CSpecParser;

/**
 * Encodes a program path as a verification condition and checks the condition
 * for validity. Also optionally checks the path for feasibility (e.g., the path
 * (x := 0; assume x > 0; assert false) is invalid but infeasible).
 */

final class PathMergeEncoder {
  private PathEncoding pathEncoding;
  private boolean runIsValid, runIsFeasible, checkFeasibility;
  private boolean succeed;
  private final static String COND_ASSUME_LABEL = "COND_ASSUME";

  PathMergeEncoder(PathEncoding pathEncoding) {
    this.pathEncoding = pathEncoding;
    checkFeasibility = false;
    reset();
  }

  static PathMergeEncoder create(PathEncoding encoding) {
    return new PathMergeEncoder(encoding);
  }

  ExpressionEncoder getExpressionEncoder() {
    return pathEncoding.getExpressionEncoder();
  }
  
  /**
   * Prepare this encoder for a new path.
   */
  void reset() {
    runIsValid = true;
    runIsFeasible = true;
  }

  /**
   * Check the current statement's pre-condition 
   * 
   * @param stmt
   *          the statement to encode
   * @return false if the statement results in an invalid verification condition
   *         or an infeasible path; true otherwise.
   */
  boolean checkPreCondition(Expression preCond, IRStatement stmt) 
      throws PathFactoryException {    

    ExpressionClosure pre = stmt.getPreCondition(pathEncoding.getExpressionEncoder());
    if (pre != null) {
      /* If the statement has a precondition, we have to check it before continuing with 
       * the encoding.
       */
      IOUtils.debug().pln("Checking pre-condition: " + pre).flush();
      ValidityResult<?> result = pathEncoding.checkAssertion(preCond, pre);

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
        SatResult<?> res = pathEncoding.checkPath(preCond);
        IOUtils.out().println("Result: " + res);
        runIsFeasible = !res.isUnsatisfiable();
      }
    }   
    return true;
  }
 
  /** Encode statement stmt, with single pre-condition */
  Expression encodeStatement(IRStatement stmt, final Expression preCond) 
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
   * return null, if encoding of one pre-path failed
   */
  Expression encodePathWithPreConds(Path currPath, final Iterable<Expression> preConds,
      final Iterable<Expression> preGuards) throws PathFactoryException {
    Preconditions.checkArgument(preConds != null && !Iterables.isEmpty(preConds));
    Preconditions.checkArgument(preGuards == null ||
        Iterables.size(preGuards) == Iterables.size(preConds));
    
    Expression preCond = null;
    
    int size = Iterables.size(preConds);
    if(size == 1)   preCond = Iterables.get(preConds, 0);
    /* more than one preConds and preGuards, merge it before encode statement */
    else    preCond = pathEncoding.noop(preConds, preGuards);      

    for(IRStatement stmt : currPath.stmts) {
      preCond = encodeStatement(stmt, preCond);
      
      /* This stmt is conditional control flow graph guard */
      if(stmt.getPreLabels().contains(COND_ASSUME_LABEL))
        currPath.addGuard(preCond);
      
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
  Expression encodePath(final Graph graph, Path currPath, Map<Path, Expression> pathExprMap) 
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
            Expression guard = prePath.guards.peek();
            if(preGuards == null) 
              preGuards = Lists.newArrayList(guard);
            else
              preGuards.add(guard);
          }
        }
        Stack<Expression> prefixGuards = (prePaths.iterator().next()).guards;
        if(prePaths.size() > 1) {
          prefixGuards.pop();
        }
        if(prefixGuards != null && !prefixGuards.isEmpty()) 
          currPath.setGuards(prefixGuards);
      }
    }
    Expression pathExpr = encodePathWithPreConds(currPath, preConds, preGuards);
    pathExprMap.put(currPath, pathExpr);
    return pathExpr;
  }
  
  Expression encodeGraph(final Graph graph) throws PathFactoryException {
    Map<Path, Expression> pathExprMap = Maps.newHashMap();
    return encodePath(graph, graph.destPath, pathExprMap);
  }
  
  boolean runIsFeasible() throws PathFactoryException {
    return runIsFeasible;
  }

  /**
   * Returns true if all verification conditions passed to handle() since the
   * last call to reset() were valid.
   */
  boolean runIsValid() {
    return runIsValid;
  }
  
  void setFeasibilityChecking(boolean b) {
    checkFeasibility = b;
  }
}

final class Path {
  final IRBasicBlock srcBlock;
  final List<IRStatement> stmts;
  final IRBasicBlock destBlock;
  Stack<Expression> guards = null;
  
  static Path createSingleton(List<? extends IRStatement> stmts) {
    if(stmts == null || stmts.isEmpty()) return null;
    return create(stmts, null, null);
  }
  
  static Path createSingleton(IRStatement stmt) {
    List<IRStatement> stmts = Lists.newArrayList(stmt);
    return create(stmts, null, null);
  }
  
  static Path create(List<? extends IRStatement> stmts, IRBasicBlock srcBlock, 
      IRBasicBlock destBlock) {
    return new Path(stmts, srcBlock, destBlock);
  }
  
  Path(List<? extends IRStatement> stmts, IRBasicBlock srcBlock, IRBasicBlock destBlock) {
    this.destBlock = destBlock;
    this.srcBlock = srcBlock;
    this.stmts = Lists.newArrayList(stmts);
  }
  
  void addGuard(Expression expr) {
    Preconditions.checkArgument(expr.isTuple());
    Expression guard = expr.asTuple().getChild(1);
    if(guards == null)  guards = new Stack<Expression>();
    guards.push(guard);
  }
  
  void setGuards(Stack<Expression> guards) {
    Preconditions.checkArgument(this.guards == null);
    this.guards = guards;
  }
  
  boolean hasGuard() {
    return guards != null && !guards.isEmpty();
  }
  
  boolean isEmpty() {
    return stmts.isEmpty();
  }
  
  boolean hasBlocks() {
    return srcBlock != null || destBlock != null;
  }
  
  IRStatement getStmt(int index) {
    Preconditions.checkArgument(index >= 0 && index < stmts.size());
    return stmts.get(index);
  }
  
  IRStatement getLastStmt() {
    Preconditions.checkArgument(stmts != null && !stmts.isEmpty());
    return stmts.get(stmts.size()-1);
  }
  
  IRBasicBlock getBlock(int index) {
    Preconditions.checkArgument(index >= 0 && index <= stmts.size());
    if(!hasBlocks())    return null;    
    if(index == 0)      return srcBlock;
    
    IRLocation pos = stmts.get(index).getLocation();
    if(srcBlock != null && pos.isWithin(srcBlock))      return srcBlock;
    if(destBlock != null && pos.isWithin(destBlock))    return destBlock;
    return getBlock(index-1);
  }
  
  List<Path> split(int index) {
    Preconditions.checkArgument(index >= 0 && index <= stmts.size());
    List<Path> resPaths = Lists.newArrayList();
    IRBasicBlock splitBlock = null;
    if(index == 0) {
      resPaths.add(null);
      resPaths.add(this);
    } else if(index == stmts.size()){
      resPaths.add(this);
      resPaths.add(null);
    } else {
      splitBlock = getBlock(index);
      Path path_1 = Path.create(stmts.subList(0, index), srcBlock, splitBlock);
      Path path_2 = Path.create(stmts.subList(index, stmts.size()), splitBlock, destBlock);
      resPaths.add(path_1);
      resPaths.add(path_2);
    }
    return resPaths;
  }
  
  static Path mergePath(Path path1, Path path2) {
    IRBasicBlock srcBlockPrime = path1.srcBlock;
    IRBasicBlock destBlockPrime = path2.destBlock;
    List<IRStatement> stmtsPrime = Lists.newArrayList(path1.stmts);
    stmtsPrime.addAll(path2.stmts);
    Path resPath = Path.create(stmtsPrime, srcBlockPrime, destBlockPrime);
    return resPath;
  }
  
  @Override
  public String toString() {
    String srcId = srcBlock == null ? "null" : srcBlock.getId().toString();
    String destId = destBlock == null ? "null" : destBlock.getId().toString();
    StringBuilder sb = new StringBuilder().append('(').append(srcId)
        .append(": ").append(destId).append(')').append(stmts);
    return sb.toString();
  }
  
  public boolean isCopyOf(Object other) {
    if(other == null)   return false;
    if(!(other instanceof Path)) return false;
    if(other == this) return true;
    Path otherPath = (Path) other;
    return srcBlock.equals(otherPath.srcBlock) && 
      destBlock.equals(otherPath.destBlock) && 
      stmts.equals(otherPath.stmts);
  }
}

final class Graph {
  private final static String COND_ASSUME_LABEL = "COND_ASSUME";
  Map<Path, Set<Path>> predecessorMap = null;
  Path srcPath = null;
  Path destPath = null;
  
  static Graph createSingleton(Path path) {
    Map<Path, Set<Path>> emptyMap = Maps.newLinkedHashMap();
    return new Graph(emptyMap, path, path);
  }
  
  static Graph create(Map<Path, Set<Path>> map, 
      Path srcPath, Path destPath) {
    return new Graph(map, srcPath, destPath);
  }
  
  Graph(Map<Path, Set<Path>> map, Path srcPath, Path destPath) {
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
  
  boolean hasEmptyMap() {
    return predecessorMap.isEmpty();
  }
  
  IRBasicBlock getDestBlock() {
    if(destPath == null)    return null;
    return destPath.destBlock;
  }
  
  IRBasicBlock getSrcBlock() {
    if(srcPath == null)     return null;
    return srcPath.srcBlock;
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
  
  void appendPreGraph(Graph preGraph) { 
    if(preGraph == null)    return;
    Map<Path, Set<Path>> preMap = preGraph.predecessorMap;
    Path preDestPath = preGraph.destPath;
  
    predecessorMap.putAll(preMap);
    if(preDestPath != srcPath) {
      Set<Path> predecessorPaths = Sets.newHashSet(preDestPath);
      predecessorMap.put(srcPath, predecessorPaths);
      srcPath = preGraph.srcPath;
    } else {
      srcPath = preGraph.srcPath;
    }
  }
  
  void appendAllPreGraph(Iterable<Graph> preGraphs) throws RunProcessorException { 
    Preconditions.checkArgument(preGraphs != null && !Iterables.isEmpty(preGraphs));
    final Path preSrcPath = Iterables.get(preGraphs, 0).srcPath;
    boolean sameSrcPath = Iterables.all(preGraphs, new Predicate<Graph>(){
      @Override
      public boolean apply(Graph graph) {
        return graph.srcPath==preSrcPath;
      }
    });
    if(!sameSrcPath)   throw new RunProcessorException("Invalid graph");
    
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
  
  void appendPostGraph(Graph postGraph) {  
    if(postGraph == null)   return;
    Map<Path, Set<Path>> postMap = postGraph.predecessorMap;
    Path postSrcPath = postGraph.srcPath;
    
    predecessorMap.putAll(postMap);
    if(postSrcPath != destPath) {
      Set<Path> predecessorPaths = Sets.newHashSet(destPath);
      predecessorMap.put(postSrcPath, predecessorPaths); 
      destPath = postGraph.destPath;
    } else {
      destPath = postGraph.destPath;
    }
  }
  
  void addInvariantPath(Path prePath, Path postPath) {
    if(prePath == null || postPath == null)    return;
    assert(srcPath == destPath);
    Set<Path> preDestPaths = predecessorMap.remove(destPath);
    predecessorMap.put(postPath, preDestPaths);
    predecessorMap.put(srcPath, Sets.newHashSet(prePath));
    srcPath = prePath;
    destPath = postPath;
  }
  
  void appendPrePath(Path path) {
    if(path == null)    return;
    predecessorMap.put(srcPath, Sets.newHashSet(path));
    srcPath = path;
  }
  
  void appendPostPath(Path path) {
    if(path == null)    return;
    predecessorMap.put(path, Sets.newHashSet(destPath));
    destPath = path;
  }
  
  private boolean hasReturnStmt(Path path) {
    if(path == null || path.isEmpty())  {
      Set<Path> prePaths = predecessorMap.get(path);
      if(prePaths.size() > 1) return false;
      Path prePath = prePaths.iterator().next();
      return hasReturnStmt(prePath);
    } else {
      IRStatement stmt = path.stmts.get(path.stmts.size()-1);
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
      IRStatement stmt = path.stmts.get(path.stmts.size()-1);
      return stmt;
    }
  }
  
  IRStatement getReturnStmt() {
    Preconditions.checkArgument(hasReturnStmt());
    return getReturnStmt(destPath);
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
      if(path.stmts.size() > 0 && 
          path.stmts.get(0).getPreLabels().contains(COND_ASSUME_LABEL)) {
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
      while(prePaths != null && prePaths.size() == 1 && (currPath.stmts.size() == 0 || 
          !currPath.stmts.get(0).getPreLabels().contains(COND_ASSUME_LABEL))) {
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
  
/*  
  List<IRStatement> collectHavocStmts(Path currPath) {
    List<IRStatement> havocStmts = Lists.newArrayList();
    
    if(!predecessorMap.containsKey(currPath)) return havocStmts;
    
    for(Path prePath : predecessorMap.get(currPath)) {
      havocStmts.addAll(collectHavocStmts(prePath));
    }
    for(IRStatement stmt : currPath.stmts) {
      if(stmt.getType() == StatementType.ASSIGN) {
        IRExpressionImpl lval = (IRExpressionImpl) ((Statement) stmt).getOperand(0);
        havocStmts.add(Statement.havoc(lval.getSourceNode(), lval));
      }           
    }
    return havocStmts;
  }*/
  
  /** find all havoc statement */
  List<IRStatement> collectHavocStmts() {
    Queue<Path> queue = Lists.newLinkedList();
    List<Path> visited = Lists.newArrayList();
    List<IRStatement> resStmts = Lists.newArrayList();
    queue.add(destPath);
    while(!queue.isEmpty()) {
      Path currPath = queue.poll();
      if(visited.contains(currPath))    continue;
      for(IRStatement stmt : currPath.stmts) {
        if(stmt.getType() == StatementType.ASSIGN) {
          IRExpressionImpl lval = (IRExpressionImpl) ((Statement) stmt).getOperand(0);
          resStmts.add(0, Statement.havoc(lval.getSourceNode(), lval));
        }           
      }
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
    Map<Path, Set<Path>> map = Maps.newLinkedHashMap(predecessorMap);
    Queue<Path> queue = Lists.newLinkedList();
    queue.add(destPath);
    
    while(!queue.isEmpty()) {
      Path path = queue.poll();
      Set<Path> prePaths = map.remove(path);
      if(prePaths == null) continue;
      for(Path prePath : prePaths) {
        if(!queue.contains(prePath))
          queue.add(prePath);
      }
    }
    
    return map.isEmpty();
  }
}

/**
 * A processor for control file runs (i.e., non-looping paths annotated
 * through the program).
 */
class RunMergeProcessor implements RunProcessor {
  
  public RunMergeProcessor(Map<File, CSymbolTable> symbolTables,
      Map<Node, IRControlFlowGraph> cfgs, CAnalyzer cAnalyzer,
      CExpressionEncoder exprEncoder)
      throws RunProcessorException {
    this.symbolTables = symbolTables;
    this.cfgs = cfgs;
    this.cAnalyzer = cAnalyzer;
    this.pathEncoder = PathMergeEncoder.create(SimplePathEncoding.create(exprEncoder));
    this.TEMP_VAR_POSTFIX = 0;
  }
  
  private final Map<File, CSymbolTable> symbolTables;
  private final Map<Node, IRControlFlowGraph> cfgs;
  private final CAnalyzer cAnalyzer;
  private final PathMergeEncoder pathEncoder;
  private int TEMP_VAR_POSTFIX;

  /**
   * Process a run: build the path through the CFG that it represents, convert
   * the path to a verification condition, then check the verification
   * condition.
   * 
   * @param run
   *          a run from a Cascade control file
   * @return true if all assertions in the run hold, false otherwise.
   * @throws RunProcessorException
   *           if an error occurred while processing the run. E.g., if the path
   *           was ill-defined, or if an unhandled statement was encountered.
   */
  
  public boolean process(Run run) throws RunProcessorException {
    try {
      
      Graph graph = processRun(run.getStartPosition(), run.getEndPosition(), 
          run.getWayPoints());
      
      Path globalPath = Path.createSingleton(CfgBuilder.getGlobalStmts(run));
      if(globalPath != null)    graph.appendPrePath(globalPath);
      graph.simplify();
      pathEncoder.encodeGraph(graph);
      return pathEncoder.runIsValid();
    } catch (PathFactoryException e) {
      throw new RunProcessorException(e);
    }
  }

  /** Incorporate the command for the given position into the given path. */
  List<IRStatement> processPosition(Position position, CSymbolTable symbolTable) 
      throws RunProcessorException {
    List<IRStatement> path = Lists.newArrayList();
    
    List<Command> cmds = position.getCommands();
    for(Command cmd : cmds) {
      try {
        String funName = cmd.getCascadeFunction();
        CSpecParser funParser = new CSpecParser(new StringReader(funName),
            position.getFile().getPath());
        Result funResult = funParser.pCSpecExpression(0);
        Node fun = (Node) funParser.value(funResult);
      
        List<String> args = cmd.getArgument();
        List<CExpression> argExprs = Lists.newArrayList();
        
        for(String arg : args) {
          CSpecParser specParser = new CSpecParser(new StringReader(arg),
              position.getFile().getPath());
          Result specResults = specParser.pCSpecExpression(0);
          Node spec = (Node) specParser.value(specResults);
        
          /*
           * TODO: modifications to the symbol table by the analyzer are ignored.
           */
          cAnalyzer.analyze(spec, symbolTable.getOriginalSymbolTable());
          IOUtils
          .debug()
          .pln("<ast>")
          .incr()
          .format(spec)
          .decr()
          .pln("\n</ast>")
          .flush();
          CExpression argExpr = CExpression.create(spec,symbolTable.getCurrentScope());
          IOUtils.debug().pln(argExpr.toString()).flush();
          argExprs.add(argExpr);
        }
        
        if (funName.trim().equals("cascade_check")) {
          path.add(Statement.assertStmt(fun, argExprs.get(0)));
        } else if (funName.trim().equals("cascade_assume")) {
          path.add(Statement.assumeStmt(fun, argExprs.get(0)));
        } else {
          throw new RunProcessorException("Unknown Cascade function: " + funName);
        }
        
      } catch (IOException e) {
        throw new RunProcessorException("Specification parse failure", e);
      } catch (ParseException e) {
        throw new RunProcessorException("Specification parse failure", e);
      }
    }

    return path;
  }

  /**
   * Find a path in the CFG to the given position and add the statements along
   * the path to the List path. If more than one path
   * to the position exists in the CFG, one will be chosen arbitrarily. Raises
   * PathBuilderException if no path to the position can be found.
   * 
   * The behavior if position is not within a basic block depends
   * on the property position.matchAfter: if true, the
   * path will terminate at the nearest subsequent block; if false,
   * it will terminate after the nearest preceding block.
   * 
   * In this implementation, the path chosen will always be the shortest path.
   * If there is more than one shortest path, one will be chosen arbitrarily.
   * 
   */
  private IRBasicBlock getTargetBlock(IRControlFlowGraph cfg,
      IRBasicBlock block, IRLocation pos) throws RunProcessorException {
    IRBasicBlock target;
    if(pos instanceof Position) {
      target = cfg.splitAt(pos, InsertionType.BEFORE.equals(
          ((Position)pos).getInsertionType()));
    } else {
      throw new RunProcessorException("Bad position: " + pos);
    }      

    if( target==null ) {
      throw new RunProcessorException("Bad position: " + pos);
    }
    IOUtils.debug().pln("Searching for path:").incr().pln(
        "Source: " + block + "\nTarget: " + target).decr().flush();
    return target;
  }
  
  /**
   * Find a path map in the CFG to the given start block and target block and 
   * store it in cfg.
   */
  private Map<IRBasicBlock, Set<IREdge<?>>> buildPathMap(IRControlFlowGraph cfg,
      IRBasicBlock start, IRBasicBlock target) throws RunProcessorException {
//    Map<IRBasicBlock, Set<IREdge<?>>> pathMap = Maps.newHashMap();
//    Set<IREdge<?>> visited = Sets.newLinkedHashSet();
//    depthFirstSearch(cfg, start, target, pathMap, visited);   
    
    Queue<List<IREdge<?>>> queue = Lists.newLinkedList();
    List<IREdge<?>> emptyList = Lists.newArrayList();
    queue.add(emptyList);
    Map<IRBasicBlock, Set<IREdge<?>>> pathMapNew = 
        breadthFirstSearch(cfg, start, target, queue);
    return pathMapNew;
  }
  
  private Map<IRBasicBlock, Set<IREdge<?>>> breadthFirstSearch(
      IRControlFlowGraph cfg,  IRBasicBlock start, IRBasicBlock target, 
      Queue<List<IREdge<?>>> queue) throws RunProcessorException {
    Map<IRBasicBlock, Set<IREdge<?>>> pathMap = Maps.newHashMap();
    boolean loop = start.equals(target); /* && start.getType().equals(IRBasicBlock.Type.LOOP);*/
    if(loop) {
      queue.remove();
      assert(queue.isEmpty());
      for (IREdge<?> ve : cfg.getIncomingEdges(target)) {
        List<IREdge<?>> path = Lists.newArrayList();
        path.add(ve);
        queue.add(path);
      }
    }
    
    while(!queue.isEmpty()) {
      /* get the first set of edges from the queue */
      List<IREdge<?>> edges = queue.poll();
      /* get the last node from the last edge */
      IRBasicBlock head = edges.isEmpty() ? target : edges.get(edges.size()-1).getSource();
      /* reach the start node */
      if(head.equals(start)) {
        for(IREdge<?> ve : edges) {
          IRBasicBlock tgt = ve.getTarget();
          Set<IREdge<?>> edgesPrime = pathMap.get(tgt);
          if(edgesPrime == null) edgesPrime = Sets.newHashSet();
          edgesPrime.add(ve);
          pathMap.put(tgt, edgesPrime);
        }
      } else {
        for(IREdge<?> ve : cfg.getIncomingEdges(head)) {
          final IRBasicBlock src = ve.getSource();
          boolean visited = Iterables.any(edges, new Predicate<IREdge<?>>(){
            @Override
            public boolean apply(IREdge<?> edge) {
             return edge.getTarget().equals(src); 
            }
          });
          if(visited && (!loop || src != start)) continue;
          
          List<IREdge<?>> edgesPrime = Lists.newArrayList(edges);
          edgesPrime.add(ve);
          queue.add(edgesPrime);
        }
      }
    }
    return pathMap;
  }
  
/*  private void depthFirstSearch(IRControlFlowGraph cfg,
      IRBasicBlock start, IRBasicBlock target, 
      Map<IRBasicBlock, Set<IREdge<?>>> pathMap, Set<IREdge<?>> visited) 
          throws RunProcessorException {
    
    if(start.equals(target) && start.getType().equals(IRBasicBlock.Type.LOOP)) {
      for (IREdge<?> e : cfg.getIncomingEdges(target)) {
        visited.add(e);
        depthFirstSearch(cfg, start, e.getSource(), pathMap, visited);
        visited.remove(e);
      }
    } else {
      for(IREdge<?> e : cfg.getIncomingEdges(target)) {
        if(visited.contains(e))   continue;
        
        IRBasicBlock v = e.getSource();
        
         Ignore the cycle 
        if(target.getType().equals(IRBasicBlock.Type.LOOP) && 
            v.getScope().getParent().equals(target.getScope()))
          continue;
        
        if(v.equals(start)) {
          visited.add(e);
          for(IREdge<?> ve : visited) {
            IRBasicBlock tgt = ve.getTarget();
            Set<IREdge<?>> edges = pathMap.get(tgt);
            if(edges == null) edges = Sets.newHashSet();
            edges.add(ve);
            pathMap.put(tgt, edges);
          }
          visited.remove(e);
          continue;
        } 
        
        visited.add(e);
        depthFirstSearch(cfg, start, v, pathMap, visited);
        visited.remove(e);
      }
    }
  }*/
  
  /**
   * Unrolling loop block for <code>iterTimes</code> times
   * @throws RunProcessorException 
   */
  Graph loopUnrolling(IRControlFlowGraph cfg, IRBasicBlock u, int iterTimes) 
      throws RunProcessorException {
    Preconditions.checkArgument(u.getType().equals(IRBasicBlock.Type.LOOP));
    Preconditions.checkArgument(iterTimes > 0);
    Graph loopGraph = null;
    while(iterTimes > 0) {
      Graph singleLoop = buildPathGraphToBlock(cfg, u, u);
      if(loopGraph == null) 
        loopGraph = singleLoop;
      else { /* Tricky part to merge two loop graph */
        // loopGraph.destPath != singleLoop.srcPath 
        assert(loopGraph.destPath.isCopyOf(singleLoop.srcPath)); 
        
        Set<Path> preLoopPaths = loopGraph.predecessorMap.remove(loopGraph.destPath);        
        loopGraph.predecessorMap.put(singleLoop.srcPath, preLoopPaths);
        
        Set<Path> preSinglePaths = singleLoop.predecessorMap.remove(singleLoop.srcPath);
        singleLoop.predecessorMap.put(loopGraph.destPath, preSinglePaths);
        
        loopGraph.predecessorMap.putAll(singleLoop.predecessorMap);
      }
      iterTimes--;
    }
    return loopGraph;
  }
  
  
  /**
   * Find a path in the CFG to the given start block and target block, and add
   * the statements along the path to the list path. 
   * If more than one path to the position exists in the CFG, one will be chosen
   * arbitrarily. Raises PathBuilderException if no path can be 
   * found.
   * 
   * In this implementation, the path chosen will always be the shortest path.
   * If there is more than one shortest path, one will be chosen arbitrarily.
   * 
   * @throws RunProcessorException
   */
  
  private Graph buildPathGraphToBlock(IRControlFlowGraph cfg,
      IRBasicBlock start, IRBasicBlock target) 
          throws RunProcessorException {
    /*
     * Find all paths from block to target, using a backwards BFS. 
     * pathMap will associate each block with its "next hops" in the path.
     */  
    Map<IRBasicBlock, Set<IREdge<?>>> pathMap = buildPathMap(cfg, start, target);

    if (pathMap == null) {
      /* The two blocks aren't connected! */
      IOUtils.err().println("No path found.");
      throw new RunProcessorException("Invalid run");
    }

    /* Build predecessor map based on path map */
    Map<Path, Set<Path>> predecessorMap = Maps.newLinkedHashMap();
    
    Map<IRBasicBlock, Path> blockPathMap = Maps.newHashMap();
    
    for(Entry<IRBasicBlock, Set<IREdge<?>>> pair : pathMap.entrySet()) {
      IRBasicBlock block = pair.getKey();
      
      /* build path for block */
      Path path = blockPathMap.get(block);
      if(path == null) {
        path = Path.create(block.getStatements(), block, block);
        blockPathMap.put(block, path);
      }
      
      /* build the set of pre-paths */
      Set<Path> prePaths = Sets.newHashSet();
      for(IREdge<?> edge : pair.getValue()) {
        IRBasicBlock srcBlock = edge.getSource();
        Path srcPath = blockPathMap.get(srcBlock);
        if(srcPath == null) {
          srcPath = Path.create(srcBlock.getStatements(), srcBlock, srcBlock);
          blockPathMap.put(srcBlock, srcPath);
        }
        
        if (edge.getGuard() != null) { // edge has guard
          Statement stmt = Statement.assumeStmt(edge.getSourceNode(), edge.getGuard());
          stmt.addPreLabel(COND_ASSUME_LABEL);
          Path edgePath  = Path.createSingleton(stmt);
          predecessorMap.put(edgePath, Sets.newHashSet(srcPath));
          prePaths.add(edgePath);
        } else {
          prePaths.add(srcPath);
        }
      }
      
      /* Unrolling loops for loop block with positive iteration times */
      if(block.getType().equals(IRBasicBlock.Type.LOOP) && 
          block.getIterTimes() > 0) {
        int iterTimes = block.getIterTimes();
        block.clearIterTimes();
        Graph loopGraph = loopUnrolling(cfg, block ,iterTimes);
        
        assert(loopGraph.destPath.isCopyOf(path));
        Set<Path> preLoopPaths = loopGraph.predecessorMap.remove(loopGraph.destPath);
        loopGraph.predecessorMap.put(path, preLoopPaths);

        Set<Path> preGraphPaths = predecessorMap.remove(path);
        predecessorMap.put(loopGraph.destPath, preGraphPaths);
        
        predecessorMap.putAll(loopGraph.predecessorMap);
        
        predecessorMap.put(loopGraph.srcPath, prePaths);
        continue;
      }
      
      predecessorMap.put(path, prePaths);
    }

    Graph graph = null;
    if(predecessorMap.isEmpty()) { // start == target and start.type != LOOP
      if(start != target || (start == target && start.getType().equals(IRBasicBlock.Type.LOOP))) 
        throw new RunProcessorException("Failure to build graph from " + start + " to " + target);
      graph = Graph.createSingleton(Path.create(start.getStatements(), start, start));
    } else {
      graph = Graph.create(predecessorMap, blockPathMap.get(start), blockPathMap.get(target));
    }
    return graph;
  }

  /**
   * Find a path in the CFG to the given start block and target block, and add
   * the statements along the path to the list path. 
   * If more than one path to the position exists in the CFG, one will be chosen
   * arbitrarily. Raises PathBuilderException if no path can be 
   * found.
   * 
   * In this implementation, the path chosen will always be the shortest path.
   * If there is more than one shortest path, one will be chosen arbitrarily.
   * 
   */
  
  /** 
  private IRBasicBlock buildPathToBlock(IRControlFlowGraph cfg,
      IRBasicBlock start, IRBasicBlock target, List<IRStatement> path) 
          throws RunProcessorException {
    
    
     * Find the shortest path from block to target, using a backwards
     * breadth-first search. pathMap will associate each block with its
     * "next hop" in the shortest path.
     
    Map<IRBasicBlock, IREdge<?>> pathMap = Maps.newHashMap();
    Set<IRBasicBlock> visited = Sets.newHashSet();
    Queue<IRBasicBlock> queue = Lists.newLinkedList();
    
     For finding a loop from start to start/target. Add incoming 
     * edges and their source nodes into pathMap and visited set
     * before entering into while-loop. It means to avoid labeling
     * start as visited node. 
    if(start.equals(target) && start.getType().equals(IRBasicBlock.Type.LOOP)) {
      for (IREdge<?> e : cfg.getIncomingEdges(start)) {
        IRBasicBlock v = e.getSource();
        if (!visited.contains(v)) {
          queue.add(v);
          pathMap.put(v, e);
        }
      }
    } else {
      queue.add(target);
    }
    
    while (!(visited.contains(start) || queue.isEmpty())) {
      IRBasicBlock u = queue.remove();
      visited.add(u);
      for (IREdge<?> e : cfg.getIncomingEdges(u)) {
        IRBasicBlock v = e.getSource();
        if (!(visited.contains(v) || queue.contains(v))) {
          queue.add(v);
          pathMap.put(v, e);
        }
      }
    }

    if (!visited.contains(start)) {
       The two blocks aren't connected! 
      IOUtils.err().println("No path found.");
      throw new RunProcessorException("Invalid run");
    }

     Add statements along the shortest path 
    IRBasicBlock u = start;
    IOUtils.debug().pln("Shortest path:").incr().flush();
    
     For finding a loop from start to start/target. Add incoming 
     * edges and their source nodes into pathMap and visited set
     * before entering into while-loop. It means to avoid labeling
     * start as visited node. 
    if(start.equals(target) && start.getType().equals(IRBasicBlock.Type.LOOP)) {
      IOUtils.debug().pln(u.toString()).flush();
      path.addAll(u.getStatements());
      IREdge<?> e = pathMap.get(u);
      assert (e != null);
      addEdgeToPath(path, e);
      u = e.getTarget();
    }
    
    while (!target.equals(u)) {
      IOUtils.debug().pln(u.toString()).flush();
      int iterTimes = u.getIterTimes();
      while(iterTimes > 0) {
        u.clearIterTimes();
        u = buildPathToBlock(cfg, u, u, path);
        iterTimes--;
      }
      path.addAll(u.getStatements());
      IREdge<?> e = pathMap.get(u);
      assert (e != null);
      addEdgeToPath(path, e);
      u = e.getTarget();
    }
    IOUtils.debug().decr().flush();

    return target;
  }*/
  
/**  
  private void addEdgeToPath(List<IRStatement> path, IREdge<?> e) {
    if (e.getGuard() != null) {
      path.add(Statement.assumeStmt(e.getSourceNode(), e.getGuard()));
    }
  }*/
  
  /**
   * Find the CFG that "contains" the given position. Since we don't track where
   * a function ends, we choose the closest match, defined as: a CFG starting on
   * line X in file F is the closest match for a position on line Y in file F
   * iff. X <= Y, and no other CFG in file F starts on line Z such that X < Z <=
   * Y.
   */
  private IRControlFlowGraph getCFGForLocation(IRLocation start) {
    IOUtils.debug().pln("Finding CFG for position: " + start);

    File file = start.getFile();
    int lineNum = start.getLine();

    Node bestNode = null;
    int bestDiff = Integer.MAX_VALUE;

    for (Node node : cfgs.keySet()) {
      Location loc = node.getLocation();
      IOUtils.debug().loc(node).p(' ');
      if (file.equals(new File(loc.file))) {
        int diff = lineNum - loc.line;
        IOUtils.debug().p("diff=" + diff + " ");
        if (diff == 0) {
          IOUtils.debug().pln("Exact match.");
          bestNode = node;
          break;
        } else if (diff > 0 && diff < bestDiff) {
          IOUtils.debug().pln("Best match so far.");
          bestNode = node;
          bestDiff = diff;
        } else {
          IOUtils.debug().pln("Not a match.");
        }
      } else {
        IOUtils.debug().pln("Wrong file.");
      }
    }
    IRControlFlowGraph cfg = cfgs.get(bestNode);
    IOUtils.debug().pln("CFG for position: " + cfg).flush();
    return cfg;
  }

  /** Find the CFG for function call Statement. */
  private IRControlFlowGraph getCFGForStatement(IRStatement stmt) 
      throws RunProcessorException {
    Node bestNode = findFuncDeclareNode(stmt);
    IRControlFlowGraph cfg = cfgs.get(bestNode);
    return cfg;
  }
  
  /** Get the function declare Node for the function call statement. */
  private Node findFuncDeclareNode (IRStatement stmt) throws RunProcessorException {
    Preconditions.checkArgument(stmt.getType().equals(StatementType.CALL));
    String funcName = ((Statement) stmt).getOperand(0).toString();    
    File file = stmt.getLocation().getFile();
    CSymbolTable symbolTable = symbolTables.get(file);
    return findFuncDeclareNode(symbolTable, funcName);
  }
  
  private Node findFuncDeclareNode (CSymbolTable symbolTable, String funcName) 
      throws RunProcessorException {
    IRVarInfo info = symbolTable.lookup(funcName);
    if(info == null)    return null; /* For undeclared function. */
    Location funcDeclareLoc = info.getDeclarationNode().getLocation();
    
    String funcFile = funcDeclareLoc.file;
    int lineNum = funcDeclareLoc.line;
    Node bestNode = null;    
    for (Node node : cfgs.keySet()) {
      Location loc = node.getLocation();
      if (funcFile.equals(loc.file)) {
        int diff = lineNum - loc.line;
        if (diff == 0) {
          bestNode = node;
          break;
        }
      }
    }
    
    if(bestNode == null) {
      /* FIXME: continue find in the parent scope or stays at root scope initially? */
      IOUtils.debug().pln("Cannot find the function declaration node for " + funcName);
    }
    return bestNode;
  }
  
  /** 
   * Collect a list Statement from function body, func is the function
   * section in the control file, might with loop position and way points
   * nested inside.
   */
  private Graph collectStmtFromFunction(IRStatement stmt) 
      throws RunProcessorException {
    return collectStmtFromFunction(stmt, null);
  }
  
  private Graph collectStmtFromFunction(IRStatement stmt, CallPoint func) 
      throws RunProcessorException {
    Graph graph = null;
    IRControlFlowGraph funcCfg = getCFGForStatement(stmt);
    if(funcCfg == null) {
      System.err.println("Cannot find cfg for statement: " + stmt);
    } else {     
      IRLocation funcStart = funcCfg.getEntry().getStartLocation();
      IRLocation funcEnd = funcCfg.getExit().getEndLocation();
      List<Position> wayPoints = null;
      if(func != null) wayPoints = func.getWayPoint();
      graph = processRun(funcStart, funcEnd, wayPoints);
    }
    return graph;
  }
  
  /** 
   * Create the assign statements from arguments to parameters. 
   * E.g. repStmt: TEMP_VAR_1 := addOne(x, TEMP_VAR_0), rmvStmt: addOne(x,returnOne());
   * repStmt is a flattened version of function call stmt, rmvStmt is not.
   * It's the reason why both are required arguments.
   */
  private List<IRStatement> assignArgToParam(IRStatement stmt) 
      throws RunProcessorException {
    return assignArgToParam(null, stmt); 
  }
  
  private List<IRStatement> assignArgToParam(IRStatement repStmt, IRStatement rmvStmt) 
      throws RunProcessorException {
    Preconditions.checkArgument(rmvStmt.getType().equals(StatementType.CALL));
      
    Node defNode = findFuncDeclareNode(rmvStmt);    
    List<IRStatement> assignments = Lists.newArrayList();
    
    if(defNode == null)     return assignments;
    
    /* Pick the new scope for the function declaration */  
    File file = new File(defNode.getLocation().file);
    CSymbolTable symbolTable = symbolTables.get(file);  
    Scope paramScope = symbolTable.getScope(defNode);
    
    Node paramDeclare = null;
    
    for(Object o : defNode.getNode(2)) {
      if(o != null) {
        if("FunctionDeclarator".equals(((Node) o).getName())) {
          o = ((Node) o).get(1);
        }
      }
      if(o != null) {
        if("ParameterTypeList".equals(((Node) o).getName())) {
          paramDeclare = ((Node) o).getNode(0);
          break;
        }
      }
    }
    
    if(paramDeclare == null)    return assignments;
    
    /* Pick all arguments */
    List<IRExpression> args = Lists.newArrayList(rmvStmt.getOperands());
    args = args.subList(1, args.size());
    
    if(repStmt != null) {
      switch(repStmt.getType()) {
      case ASSIGN: {
        Node argNode = ((Statement) repStmt).getOperand(1).getSourceNode().getNode(1); 
        for(int i=0; i<args.size(); i++) {
          Node arg_call = args.get(i).getSourceNode();
          Node arg_assign = argNode.getNode(i);
          if(!arg_call.equals(arg_assign)) {
            if(!arg_assign.getString(0).startsWith(TEMP_VAR_PREFIX)) {
              throw new RunProcessorException("Invalid argument: " + arg_assign);
            }
            args.set(i, CExpression.create(arg_assign, symbolTable.getScope(arg_assign)));
          }      
        }
        break;
      }
      case CALL: {
        List<IRExpression> args_call = Lists.newArrayList(((Statement) repStmt).getOperands());
        args_call = args_call.subList(1, args_call.size());
        for(int i=0; i<args.size(); i++) {
          IRExpression arg = args.get(i);
          IRExpression arg_call = args_call.get(i);
          if(!arg_call.equals(arg)) {
            if(!arg_call.getSourceNode().getString(0).startsWith(TEMP_VAR_PREFIX)) {
              throw new RunProcessorException("Invalid argument: " + arg_call);
            }
            args.set(i, arg_call);
          }      
        }
        break;
      }
      default :
        throw new RunProcessorException("Invalid stmt type: " + repStmt);
      }
      /* Go through all arguments to replace the function call argument with corresponding 
       * temporal variable within stmt_assign. */

    }
    
    if(paramDeclare.size() != args.size()) {
      throw new RunProcessorException("#arg does not match with #param.");
    }
    /* Generate assign statement one by one */
    for(int i=0; i < paramDeclare.size(); i++) {
      Node paramNode = paramDeclare.getNode(i);
      paramNode = paramNode.getNode(1);
      /* Pointer parameter declaration */
      if("PointerDeclarator".equals(paramNode.getName()))
        paramNode = paramNode.getNode(1);
      
      assert("SimpleDeclarator".equals(paramNode.getName()));
      IRExpressionImpl param = CExpression.create(paramNode, paramScope);
      IRExpressionImpl arg = (IRExpressionImpl) args.get(i);
      Node assignNode = GNode.create("AssignmentExpression", 
          paramNode, "=", arg.getSourceNode());
      assignNode.setLocation(paramNode.getLocation());
      Statement assign = Statement.assign(assignNode, param, arg);
      assignments.add(assign);
    }    
    return assignments; 
  }

  /** Replace the last return statement as assign statement. */
  private IRStatement replaceReturnStmt(IRStatement returnStmt, IRStatement assignStmt) 
      throws RunProcessorException {
    Preconditions.checkArgument(returnStmt.getType().equals(StatementType.RETURN));
    IRExpressionImpl lExpr = (IRExpressionImpl) ((Statement) assignStmt).getOperand(0);
    IRExpressionImpl rExpr = (IRExpressionImpl) ((Statement) returnStmt).getOperand(0);
    Node assignNode = GNode.create("AssignmentExpression", 
        lExpr.getSourceNode(), "=", rExpr.getSourceNode());
    assignNode.setLocation(assignStmt.getSourceNode().getLocation());
    IRStatement assignResult = Statement.assign(assignNode, lExpr, rExpr);
    return assignResult;
  }
  
  /**
   * Function inlining for call statement
   * 1) assign statements to assign arguments to parameters, 
   * 2) statements collected from the function body.
   * 3) return statement
   */
  private Graph getGraphForAssignCallStmt(IRStatement lhsStmt, IRStatement rhsStmt, CallPoint func) 
      throws RunProcessorException {
      List<IRStatement> paramPassStmts = assignArgToParam(lhsStmt, rhsStmt);
      Graph funcGraph = collectStmtFromFunction(rhsStmt, func);
      funcGraph.appendPrePath(Path.createSingleton(paramPassStmts));
      
      /* Pick the last statement from func_path - return statement. */
      if(funcGraph.hasReturnStmt()) {
        IRStatement returnStmt = funcGraph.getReturnStmt();
        IRStatement replaceStmt = replaceReturnStmt(returnStmt, lhsStmt);
        funcGraph.appendPostPath(Path.createSingleton(replaceStmt));
      }
      return funcGraph;
  }
  
  /**
   * Function inlining for call statement
   * 1) assign statements to assign arguments to parameters, 
   * 2) statements collected from the function body.
   */
  private Graph getGraphForCallStmt(IRStatement stmt) throws RunProcessorException {
    return getGraphForCallStmt(stmt, null);
  }
    
  private Graph getGraphForCallStmt(IRStatement stmt, CallPoint func) throws RunProcessorException {
    Preconditions.checkArgument(stmt.getType().equals(StatementType.CALL));
    List<IRStatement> funcPath = assignArgToParam(stmt);
    Graph funcGraph = null;
    if(func != null)    funcGraph = collectStmtFromFunction(stmt, func);
    else                funcGraph = collectStmtFromFunction(stmt);
    funcGraph.appendPrePath(Path.createSingleton(funcPath));
    return funcGraph;
  }
  
  /**
   * Replace all the function call node with a temporary var node, and return the 
   * function call node list to keep the insertion order of the "pairs", otherwise, 
   * "pairs" will be arbitrary order.
   */  
  private LinkedHashMap<Node, Node> replaceFuncCallwithVar(Node node,
      CSymbolTable symbolTable, Scope scope) 
      throws RunProcessorException {
    Node resNode = node; 
    LinkedHashMap<Node, Node> funcNodeReplaceMap = Maps.newLinkedHashMap();
    /* replace operands of node if we can find the replace candidate operands 
     * from "funcNodeReplaceMap"
     */
    if(!node.isEmpty()) {
      /* Collect operands of node */
      boolean updated = false;
      List<Object> argList = Lists.newArrayList();
      for(int i=0; i<node.size(); i++) {
        Object arg = node.get(i);
        Object substituteArg = arg;
        if(arg instanceof Node) {
          Node argNode = (Node) arg;
          /* update "argList" if we can find new pair by step into the operands of arg */
          funcNodeReplaceMap.putAll(replaceFuncCallwithVar(argNode, symbolTable, scope));
          if(funcNodeReplaceMap.containsKey(argNode)) { /* substitute arg */
            substituteArg = funcNodeReplaceMap.get(argNode);
            updated = true;
          }
        }
        argList.add(substituteArg);
      }
      if(updated) { /* compose a substituted node */
        resNode = createNodeWithArgList(node.getName(), argList);
        resNode.setLocation(node.getLocation());
        resNode.setProperty(xtc.Constants.SCOPE, scope.getQualifiedName());
      }
    } 
    
    /* build pairs by replace function call to temp_var if such function call
     * node hasn't been replaced before
     */
    if(!funcNodeReplaceMap.containsKey(resNode) && "FunctionCall".equals(resNode.getName())) {
      String resFuncName = resNode.getNode(0).getString(0);
      if(!ReservedFunctions.contains(resFuncName)) {
        if(symbolTable.lookup(resFuncName) == null)
          throw new RunProcessorException("Undeclared function: " + resFuncName);
        /* Create temporary variable node for function call node. */
        String varName = TEMP_VAR_PREFIX + (TEMP_VAR_POSTFIX++);
        GNode varNode = GNode.create("PrimaryIdentifier", varName);
        varNode.setLocation(node.getLocation());
        varNode.setProperty(xtc.Constants.SCOPE, scope.getQualifiedName());
        varNode.setProperty(xtc.Constants.TYPE, NumberT.INT);
        if(node.equals(resNode)) {
          funcNodeReplaceMap.put(node, (Node)varNode); // f(a) : TEMP_VAR_x
        } else {
          funcNodeReplaceMap.put(node, resNode); // g(f(a)) : g(TEMP_VAR_x1)
          funcNodeReplaceMap.put(resNode, (Node)varNode); // g(TEMP_VAR_x1) : TEMP_VAR_x2
        }
        IRVarInfo varInfo = new VarInfo(scope, varName, IRIntegerType.getInstance(), varNode);

        Scope oldScope = symbolTable.getCurrentScope();
        symbolTable.setScope(scope);
        symbolTable.define(varName, varInfo);
        symbolTable.setScope(oldScope);
      } else {
        if(!node.equals(resNode))  funcNodeReplaceMap.put(node, resNode);
      }
    } else {
      if(!node.equals(resNode))  funcNodeReplaceMap.put(node, resNode);
    }
    return funcNodeReplaceMap;
  }
  
  /** Flatten function call statement if it has function call nested inside. */
  private List<IRStatement> pickFuncCallFromStmt(IRStatement stmt, CSymbolTable symbolTable) 
      throws RunProcessorException {  
    Preconditions.checkArgument(stmt != null);
    
    ImmutableList<IRExpression> argExprs = stmt.getOperands();
    List<IRExpression> argExprsRep = Lists.newArrayList();
    LinkedHashMap<Node, Node> pairs = Maps.newLinkedHashMap();
    
    for(IRExpression argExpr : argExprs) {
      Node argNode = argExpr.getSourceNode();
      Scope scope = argExpr.getScope();
      Map<Node, Node> argPairs = replaceFuncCallwithVar(argNode, symbolTable, scope);
      pairs.putAll(argPairs);
      if(argPairs.isEmpty())
        argExprsRep.add(argExpr);
      else {
        while(argPairs.get(argNode) != null)
          argNode = argPairs.get(argNode);
        argExprsRep.add(CExpression.create(argNode, scope));
      }
    }

    List<IRStatement> assignStmts = null;
    
    if(!pairs.isEmpty())    
      assignStmts = Lists.newArrayList();
    
    for(Entry<Node, Node> pair : pairs.entrySet()) {
      Node keyNode = pair.getKey();
      Node valNode = pair.getValue();
      /* For f(a) = TEMP_VAR_x, add assign statement TEMP_VAR_x := f(a) */
      if(!("FunctionCall".equals(keyNode.getName()) && 
          "PrimaryIdentifier".equals(valNode.getName())))   continue;
      Scope scope = symbolTable.getScope(valNode);
      CExpression keyExpr = CExpression.create(keyNode, scope);
      CExpression valExpr = CExpression.create(valNode, scope);
      
      Node assignNode = substituteNode(stmt.getSourceNode(), valNode, keyNode);
      IRStatement assignStmt = Statement.assign(assignNode, valExpr, keyExpr);
      assignStmts.add(assignStmt);
    }
    
    if(!pairs.isEmpty()) {
      IRStatement replaceStmt = null;
      Node replaceNode = substituteNode(stmt.getSourceNode(), argExprsRep);
      switch(stmt.getType()) {
      case ASSIGN:
        replaceStmt = Statement.assign(replaceNode, 
            (IRExpressionImpl) argExprsRep.get(0), (IRExpressionImpl) argExprsRep.get(1));
        break;
      case ASSERT:
        replaceStmt = Statement.assertStmt(replaceNode, argExprsRep.get(0)); break;
      case ASSUME:
      case AWAIT:
        replaceStmt = Statement.assumeStmt(replaceNode, argExprsRep.get(0)); break;
      case RETURN:
        replaceStmt = Statement.returnStmt(replaceNode, argExprsRep.get(0)); break;
      case CALL:
        replaceStmt = Statement.functionCall(replaceNode, 
            argExprsRep.get(0), argExprsRep.subList(1, argExprsRep.size())); break;
      default:
        throw new RunProcessorException("Invalid stmt type: " + stmt);
      }
      assignStmts.add(replaceStmt);
    }
    return assignStmts;
  }
 
  /**
   * Substitute the rhs of each element in pathRep with the related element of 
   * pathRmv. The element in pathRep is in form as "TEMP_VAR_0 := addOne(x)". 
   * addOne(x) is created in stmt is generated based on symbolTable, whose info is incorrect.
   * 
   * But, pathRmv's element has the corresponding statement - addOne(x) directly 
   * picked from cfg, whose info is correct. Here, we substitute the "addOne(x)" 
   * in pathRep to the "addOne(x)" in pathRmv.
   */
  private Graph getGraphForAllAssignCallStmt(List<IRStatement> pathRep, List<IRStatement> pathRmv) 
      throws RunProcessorException {
    return getGraphForAllAssignCallStmt(pathRep, pathRmv, null);
  }
  
  private Graph getGraphForAllAssignCallStmt(List<IRStatement> pathRep, List<IRStatement> pathRmv, 
      List<CallPoint> funcs) throws RunProcessorException {
    Preconditions.checkArgument(pathRep.size() == pathRmv.size());
    
    Graph graph = null;
    int lastIndex = pathRep.size()-1;
    for(int i=0; i<lastIndex; i++) {
      IRStatement stmtRep = pathRep.get(i);
      IRStatement stmtRmv = pathRmv.get(i);
      CallPoint func = null;
      if(funcs != null) {
        Node funcNode = stmtRmv.getSourceNode();
        assert(funcNode.getName().equals("FunctionCall") 
            && funcNode.getNode(0).getName().equals("PrimaryIdentifier"));
        String funcName = funcNode.getNode(0).getString(0);
        Iterator<CallPoint> itr = funcs.iterator();
        while(itr.hasNext()) {
          CallPoint callPos = itr.next();
          if(callPos.getFuncName().equals(funcName)) {
            func = callPos;
            itr.remove();
            break;
          }
        }
      }
      Graph tmpGraph = getGraphForAssignCallStmt(stmtRep, stmtRmv, func);
      if(graph == null)     graph = tmpGraph;
      else                  graph.appendPostGraph(tmpGraph);
    }
    
    if(graph == null)   throw new RunProcessorException("Invalid graph.");
    graph.appendPostPath(Path.createSingleton(pathRep.get(lastIndex)));
    return graph;
  }
 
  /**
   * callPos is not null, it means we are process the function call statement with 
   * specification of the symbolic run in the control file; and the path is the 
   * statements flatten from that single function call statement.
   * @throws RunProcessorException
   */
  private Graph functionInlineGraph(CSymbolTable symbolTable, Graph graph) 
      throws RunProcessorException {
    /* Map the function path to its graph */
    Map<Path, Graph> funcPathMap = Maps.newHashMap();
    
    /* BFS traverse the graph's paths, collect those with function call statement */
    Queue<Path> queue = Lists.newLinkedList();
    queue.add(graph.destPath);
    List<Path> visited = Lists.newLinkedList();
    while(!queue.isEmpty()) {
      Path currPath = queue.poll();
      if(visited.contains(currPath))    continue;
      
      if(Iterables.any(currPath.stmts, new Predicate<IRStatement>(){
        @Override
        public boolean apply(IRStatement stmt) {
          boolean res = false;
          try {
            res = stmt.getType().equals(StatementType.CALL) && 
                findFuncDeclareNode(stmt) != null;
          } catch (RunProcessorException e) {
            IOUtils.err().println(e.getStackTrace());
          }
          return res;
        }})) {
        funcPathMap.put(currPath, null);
      }
      Set<Path> prePaths = graph.predecessorMap.get(currPath);
      visited.add(currPath);
      if(prePaths != null)  queue.addAll(prePaths);     
    }
    
//    IOUtils.err().println("Function path size: " + funcPathMap.size());
    
    /* No function call, no change */
    if(funcPathMap.size() == 0) return graph;
    
    /* Call function inlining for each path with function call */
    for(Path keyPath : funcPathMap.keySet()) {
      Graph funcGraph = functionInlinePath(symbolTable, keyPath);
      funcPathMap.put(keyPath, funcGraph);
    }
    
    /* Generate a new graph predecessor map */
    Map<Path, Set<Path>> predecessorMap = Maps.newHashMap();
    
    for(Entry<Path, Set<Path>> entry : graph.predecessorMap.entrySet()) { 
      Set<Path> prePaths = Sets.newHashSet(entry.getValue());
      /* Update the value, if contains function call path */
      for(Path prePath : entry.getValue()) {
        if(funcPathMap.containsKey(prePath)) {
          Graph funcGraph = funcPathMap.get(prePath);
          prePaths.remove(prePath);
          prePaths.add(funcGraph.destPath);
        }
      }
      
      /* Update the key, if it is function call path */
      Path keyPath = entry.getKey();
      if(funcPathMap.containsKey(keyPath)) {
        Graph funcGraph = funcPathMap.get(keyPath);
        predecessorMap.put(funcGraph.srcPath, prePaths);
      } else {
        predecessorMap.put(keyPath, prePaths);
      }
    }
    
    for(Path keyPath : funcPathMap.keySet())
      predecessorMap.putAll(funcPathMap.get(keyPath).predecessorMap);
    
    Path srcPath = funcPathMap.containsKey(graph.srcPath) ? 
        funcPathMap.get(graph.srcPath).srcPath : graph.srcPath;
    Path destPath = funcPathMap.containsKey(graph.destPath) ? 
        funcPathMap.get(graph.destPath).destPath : graph.destPath;
    
    return Graph.create(predecessorMap, srcPath, destPath);
  }
  
  private boolean hasFunctionCall(IRStatement stmt) throws RunProcessorException {
    File file = stmt.getLocation().getFile();
    CSymbolTable symbolTable = symbolTables.get(file);
    return hasFunctionCall(symbolTable, stmt.getSourceNode());
  }
  
  private boolean hasFunctionCall(CSymbolTable symbolTable, Node srcNode) 
      throws RunProcessorException {
    if(srcNode.getName().equals("FunctionCall")) {
      String funcName = srcNode.getNode(0).getString(0);
      /* Do not touch the reserved functions */
      if(ReservedFunctions.contains(funcName))  return false;
      Node funcNode = findFuncDeclareNode(symbolTable, funcName);
      return (funcNode != null);
    }
    for(int i=0; i<srcNode.size(); i++) {
      Object arg = srcNode.get(i);
      if(arg instanceof Node)
        if(hasFunctionCall(symbolTable, (Node) arg))
          return true;
    }
    return false;
  }
  
/** 
   private Graph functionInlineGraph(CSymbolTable symbolTable, final Graph graph, Path destPath,
      Map<Path, Graph> pathGraphMap) throws RunProcessorException {
    Preconditions.checkArgument(graph != null);
    
    Graph destGraph = functionInlinePath(symbolTable, destPath);
    
    if(destGraph == null)    
      throw new RunProcessorException("Invalid graph for path: " + destPath);
    
    Map<Path, Set<Path>> map = graph.predecessorMap;    
    if(map.containsKey(destPath)) {
      Set<Path> prePaths = map.get(destPath);  
      List<Graph> preGraphs = Lists.newArrayList();
      for(Path prePath : prePaths) {
        Graph preGraph = pathGraphMap.containsKey(prePath) ? 
            pathGraphMap.get(prePath) : 
              functionInlineGraph(symbolTable, graph, prePath, pathGraphMap);
        preGraphs.add(preGraph);
      }
      destGraph.appendAllPreGraph(preGraphs);
    }
    pathGraphMap.put(destPath, destGraph);
    return destGraph;
  }
  
  private Graph functionInlineGraph(CSymbolTable symbolTable, Graph graph) 
      throws RunProcessorException {
    Map<Path, Graph> pathGraphMap = Maps.newHashMap();
    return functionInlineGraph(symbolTable, graph, graph.destPath, pathGraphMap);
  }
  */
  
  private CallPoint findCallPointForStmt(IRStatement stmt, List<CallPoint> callPoints) {
    Preconditions.checkArgument(stmt.getType().equals(StatementType.CALL));
    
    for(int i = callPoints.size()-1; i >=0; i++) {
      CallPoint call = callPoints.get(i);
      String name1 = call.getFuncName();
      String name2 = ((Statement) stmt).getOperand(0).toString();
      if(name1.equals(name2)) {
        callPoints.remove(i);
        return call;
      }
    }
    return null;
  }
  
  private Graph functionInlinePath(CSymbolTable symbolTable, Path path) 
      throws RunProcessorException {    
    return functionInlinePath(symbolTable, path, null);
  }
    
  private Graph functionInlinePath(CSymbolTable symbolTable, Path path, 
      Position callPos) throws RunProcessorException {
    Preconditions.checkArgument(path != null);
    
    Graph resGraph = null;
    Path tmpPath = path;
    List<CallPoint> funcs = null;
    if(callPos != null) funcs = Lists.newArrayList(callPos.getFunctions());
    while(tmpPath != null && !tmpPath.isEmpty()) {
      
      int lastIndex = tmpPath.stmts.size()-1;
      IRStatement last_stmt = tmpPath.getLastStmt();
      
      /* function call statement f(x) with declared function */
      if(last_stmt.getType().equals(StatementType.CALL) && 
          findFuncDeclareNode(last_stmt) != null) {
        
        IRStatement funcCallStmt = last_stmt;
        int splitIndex = lastIndex;
        
        List<IRStatement> stmtRep = pickFuncCallFromStmt(last_stmt, symbolTable);
        /* special case function with function as argument f(g(x), 1) */
        if(stmtRep != null && !stmtRep.isEmpty()) { 
          splitIndex = lastIndex - stmtRep.size() + 1;
          funcCallStmt = stmtRep.get(stmtRep.size()-1);
        }
        List<Path> paths = tmpPath.split(splitIndex);
        tmpPath = paths.get(0);
        
        Graph callGraph = null;
        if(funcs != null) {
          CallPoint call = findCallPointForStmt(funcCallStmt, funcs);
          callGraph = getGraphForCallStmt(funcCallStmt, call);
        } else {
          callGraph = getGraphForCallStmt(funcCallStmt);
        }
        if(resGraph == null)    resGraph = callGraph;
        else                    resGraph.appendPreGraph(callGraph);
      }
      
      /* assign statement with function call as rhs y = f(x) */
      else if(hasFunctionCall(last_stmt)) {
        List<IRStatement> stmtRep = pickFuncCallFromStmt(last_stmt, symbolTable);
        int splitIndex = lastIndex - stmtRep.size() + 1;
        List<Path> paths = tmpPath.split(splitIndex);
        tmpPath = paths.get(0);       
        Path funcPath = paths.get(1);
        Graph callGraph = null;
        if(callPos != null) {
          callGraph = getGraphForAllAssignCallStmt(stmtRep, funcPath.stmts, callPos.getFunctions());
        } else {
          callGraph = getGraphForAllAssignCallStmt(stmtRep, funcPath.stmts);
        }
        if(resGraph == null)    resGraph = callGraph;
        else                    resGraph.appendPreGraph(callGraph);
      } 
      
      /* other statements keep unchanged */
      else {
        int currIndex = lastIndex;
        while(currIndex >= 0) {
          IRStatement stmt = tmpPath.getStmt(currIndex);
          if(stmt.getType().equals(StatementType.CALL) && 
              findFuncDeclareNode(stmt) != null)
            break;
          else if(hasFunctionCall(stmt))
            break;
          else
            currIndex--;
        }

        int splitIndex = currIndex + 1;
        List<Path> paths = tmpPath.split(splitIndex);
        tmpPath = paths.get(0);
        Graph preGraph = Graph.createSingleton(paths.get(1));
        if(resGraph == null)    resGraph = preGraph;
        else                    resGraph.appendPreGraph(preGraph);
      }
    }
    return resGraph;
  }
  
  /**
   * Add tmpPath into path, before do that, check the tmpPath by call 
   * checkPath(...), and clear the tmpPath.
   */
/**  private void addTmpPathToPath(List<IRStatement> path, List<IRStatement> tmpPath, 
      CSymbolTable symbolTable) throws RunProcessorException {
    tmpPath = checkPath(symbolTable, tmpPath);
    path.addAll(tmpPath);
  }*/
  
  /** Remove way points before callPoint from wayPoints, return them. */
  private List<Position> waypointsBeforeCall(List<Position> wayPoints) 
      throws RunProcessorException {
    List<Position> resWaypoints = Lists.newArrayList();
    while(!wayPoints.isEmpty()) {
      Position waypoint = wayPoints.get(0);
      if(!waypoint.hasFunctions()) {
        Position pos = wayPoints.remove(0);
        resWaypoints.add(pos);
      }
      else
        break;
    }
    return resWaypoints;
  }
  
  /** Parse the invariant of loop. */
  private Graph processInvariant(IRControlFlowGraph cfg, Position position, 
      CSymbolTable symbolTable) throws RunProcessorException {
    Graph invariantGraph = null;
    try {
      CSpecParser specParser = new CSpecParser(new StringReader(position.getInvariant()),
          position.getFile().getPath());
      Result specResults = specParser.pCSpecExpression(0);
      Node spec = (Node) specParser.value(specResults);
      
      CExpression argExpr = CExpression.create(spec,symbolTable.getCurrentScope());
      IOUtils.debug().pln(argExpr.toString()).flush();
      
      assert(position.getLoops().size() == 1); 
      /* Pick all statements from the loop body */
      Graph loopGraph = processRun(position, position, 
          position.getLoops().iterator().next().getWayPoint());
      List<IRStatement> preStmts = Lists.newArrayList();
      
      /** FIXME: CVC4 has incremental support problem, multiple queries are not supported
       * well. If this assertion statement is added, will have invalid memory access inside
       * CVC4*/
      preStmts.add(Statement.assertStmt(spec, argExpr));      
      /* Process havoc statements */
      List<IRStatement> havocStmts = loopGraph.collectHavocStmts();
      preStmts.addAll(havocStmts.subList(0, havocStmts.size()-1));
      preStmts.add(Statement.assumeStmt(spec, argExpr));

      List<IRStatement> postStmts = Lists.newArrayList();
      postStmts.addAll(loopGraph.destPath.stmts);
      postStmts.add(Statement.assertStmt(spec, argExpr));
      
      invariantGraph = loopGraph;
      loopGraph.addInvariantPath(Path.createSingleton(preStmts), 
          Path.createSingleton(postStmts));
      
    } catch (IOException e) {
      throw new RunProcessorException("Specification parse failure", e);
    } catch (ParseException e) {
      throw new RunProcessorException("Specification parse failure", e);
    }
    return invariantGraph;    
  }
  
  private List<Position> loopPointsUnroll(IRControlFlowGraph cfg, List<Position> wayPoints) 
      throws RunProcessorException {
    List<Position> resWaypoints = Lists.newArrayList();
    for(Position pos : wayPoints) {
      if(pos.hasLoop()) {
        /* Clear default iteration times if users specify it in ctrl file */
        cfg.bestBlockForPosition(pos).clearIterTimes();
       
        for(LoopPoint loopPos : pos.getLoops()) { 
          /* Ignore loop iteration times when have loop invariant */
          if(loopPos.getInvariant() != null) {
            pos.setInvariant(loopPos.getInvariant());
            resWaypoints.add(pos);
            continue;
          }
          int iterTimes = loopPos.getIterTimes();
          while(iterTimes>0) {
            resWaypoints.add(pos);
            resWaypoints.addAll(loopPointsUnroll(cfg, loopPos.getWayPoint()));
            iterTimes--;
          }
          
          LoopPoint lastLoopPos = pos.getLoops().get(pos.getLoops().size()-1);
          /* if last loop point doesn't contains wayPoint, add iteration times 
           * to hit the entry block of the loop and exit
           */
          if(lastLoopPos.getWayPoint().isEmpty()) 
            resWaypoints.add(pos);
        }
      } else {
        resWaypoints.add(pos);
      }
    }
    return resWaypoints;
  }
  
  private Graph processRun(IRLocation start, IRLocation end, List<Position> waypoints) 
          throws RunProcessorException {   
    File file = start.getFile();
    CSymbolTable symbolTable = symbolTables.get(file);   
    IRControlFlowGraph cfg = getCFGForLocation(start);
    Scope oldScope = symbolTable.getCurrentScope();
    symbolTable.enterScope(cfg);
    
    Graph graph = null;
    IRBasicBlock block = null;
    Path startPath = null;
    Path endPath = null;

    /* Start position */
    {
      IOUtils.debug().pln("<startPosition> " + start.toString()).flush();      
      if(start instanceof Position)
        startPath = Path.createSingleton(processPosition((Position)start, symbolTable));
      
      block = cfg.splitAt(start, true);
    }
    
    if(waypoints != null && !waypoints.isEmpty()) { 
      List<Position> wayPoints = loopPointsUnroll(cfg, waypoints);
      
      while(!wayPoints.isEmpty()) {
        
        /* Way points before call position */        
        List<Position> tmpWaypoints = waypointsBeforeCall(wayPoints);
        for(Position pos : tmpWaypoints) {
          if (block == null)      break;
          IOUtils.debug().pln("<wayPoint> " + pos.toString()).flush();
          
          IRBasicBlock target = getTargetBlock(cfg, block, pos);
          Graph wayGraph = buildPathGraphToBlock(cfg, block, target);
          block = cfg.splitAt(pos, false);
          
          Scope currScope = symbolTable.getCurrentScope();
          if(block.getScope() != null)   symbolTable.setScope(block.getScope());
          if(pos.getInvariant() != null) {
            Graph invariantGraph = processInvariant(cfg, pos, symbolTable);
            block = cfg.splitAt(pos, false);
            
            wayGraph.appendPostGraph(invariantGraph);        
          }
          
          Path wayPath = Path.createSingleton(processPosition(pos, symbolTable));
          wayGraph.appendPostPath(wayPath);
          symbolTable.setScope(currScope);
          
          if(graph == null)     graph = wayGraph;
          else                  graph.appendPostGraph(wayGraph);
        }
        
        if(wayPoints.isEmpty())   break;

        /* The blocks from last way point to the call position (not include call position) */       
        Position callPos = wayPoints.remove(0);
        IOUtils.debug().pln("<callPoint> " + callPos.toString()).flush();
        
        { /* Split before callPos, target before the call position */
          IRBasicBlock target = cfg.splitAt(callPos, true, false); 
          Graph wayGraph = buildPathGraphToBlock(cfg, block, target);
          /* Split before callPos, block after the call position */
          block = cfg.splitAt(callPos, true, false);
          
          if(graph == null)     graph = wayGraph;
          else                  graph.appendPostGraph(wayGraph);
        }
        
        /* Call position */
        {
          IRBasicBlock target = cfg.splitAt(callPos, false, false);
          /* statements after flatten the function call */
          Graph targetGraph = buildPathGraphToBlock(cfg, block, target);
          assert(targetGraph.srcPath == targetGraph.destPath);
          Path targetPath = targetGraph.srcPath;
          Graph callGraph = functionInlinePath(symbolTable, targetPath, callPos);
          graph.appendPostGraph(callGraph);
          
          block = cfg.splitAt(callPos, false);
        }
      }
    }
    
    /* End position */
    if (block == null)
      throw new RunProcessorException("Function ended before end of run.");
    
    {
      IRBasicBlock endBlock = null;
      if (end == null) {
        endBlock = cfg.getExit();
        IOUtils.debug().pln("<endPosition> Null").flush();
      } else {
        endBlock = getTargetBlock(cfg, block, end);
        IOUtils.debug().pln("<endPosition> " + end.toString()).flush();
        endPath = Path.createSingleton(processPosition((Position)end, symbolTable));
      }
      Graph endGraph = buildPathGraphToBlock(cfg, block, endBlock);   
      Scope currScope = symbolTable.getCurrentScope();
      if(endBlock.getScope() != null) symbolTable.setScope(endBlock.getScope());
      
      if(graph == null)     graph = endGraph;
      else                  graph.appendPostGraph(endGraph);
      
      symbolTable.setScope(currScope);
        
    }
    
    graph.appendPrePath(startPath);
    graph.appendPostPath(endPath);
//    graph.simplify();
    graph = functionInlineGraph(symbolTable, graph);
    assert(graph.isValid());
    symbolTable.setScope(oldScope);
    
    return graph;
  }
  
  /** Substitute the child nodes in srcNode as nodes in order */
  private Node substituteNode(Node srcNode, Node ... nodes) {
    String srcNodeName = srcNode.getName();
    List<Object> argList = Lists.newArrayList();
    List<Node> candidateList = Lists.newArrayList(nodes);
    for(int i = 0; i < srcNode.size(); i++) {
      Object o = srcNode.get(i);
      if(o instanceof GNode)
        argList.add(candidateList.remove(0));
      else  
        argList.add(srcNode.get(i));
    }
    Node newNode = createNodeWithArgList(srcNodeName, argList);
    newNode.setLocation(srcNode.getLocation());
    return newNode;
  }
  
  /** Substitute the child nodes in srcNode as source nodes of <code>exprs</code> */
  private Node substituteNode(Node srcNode, List<IRExpression> exprs) {
    String srcNodeName = srcNode.getName();
    List<Object> argList = Lists.newArrayList();
    List<Node> candidateList = Lists.newArrayList();
    for(IRExpression expr : exprs)
      candidateList.add(expr.getSourceNode());
    for(int i = 0; i < srcNode.size(); i++) {
      Object o = srcNode.get(i);
      if(o instanceof GNode)
        argList.add(candidateList.remove(0));
      else  
        argList.add(o);
    }
    Node newNode = createNodeWithArgList(srcNodeName, argList);
    newNode.setLocation(srcNode.getLocation());
    return newNode;
  }
  
  /**
   * Put argList to operands, since if use GNode.create(name, argList), 
   * then newly created node has only one operand - argList. Here, 
   * we want to new node has multiple operands, each operand is an arg of argList, 
   * thus we use GNode.create(name, operands), where operands is with type
   * Pair<? extends Object>.
   */  
  private Node createNodeWithArgList(String name, List<Object> argList) {
    Pair<Object> operands = null;
    for(Object o : argList) {
      Pair<Object> pair = new Pair<Object>(o);
      if(operands == null)  operands = pair;
      else  operands = operands.append(pair);
    }
    GNode newNode = GNode.createFromPair(name, operands);
    return newNode;
  }
  
  public void enableFeasibilityChecking() {
    pathEncoder.setFeasibilityChecking(true);
  }
}