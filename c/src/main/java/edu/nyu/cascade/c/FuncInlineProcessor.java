package edu.nyu.cascade.c;

import java.io.File;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import xtc.tree.GNode;
import xtc.tree.Node;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Table;

import edu.nyu.cascade.control.CallPoint;
import edu.nyu.cascade.control.LoopPoint;
import edu.nyu.cascade.control.Position;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRStatement.StatementType;
import edu.nyu.cascade.ir.impl.IRExpressionImpl;
import edu.nyu.cascade.ir.impl.Statement;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;

public class FuncInlineProcessor {
	
  private final Map<Node, IRControlFlowGraph> cfgs;
  private final Map<String, Node> functions;
  private final RunProcessor<PathGraph> processor;
  private final Map<File, CSymbolTable> symbolTables;
  private final int effortLevel;
  
  /** Map from control flow graph of a function to a path graph */
  private final Map<IRControlFlowGraph, PathGraph> 
  	funcGraphMap = Maps.newHashMap();
  
  /** 
   * Table from control flow graph, and a collection of specified
   * way points of a function to a path graph
   */ 
  private final Table<IRControlFlowGraph, Collection<Position>, PathGraph> 
  	funcWithCallGraphTable = HashBasedTable.create();
	
  private FuncInlineProcessor(
  		RunProcessor<PathGraph> processor,
      Map<Node, IRControlFlowGraph> cfgs,
      Map<File, CSymbolTable> symbolTables,
      int effortLevel) {
    this.cfgs = cfgs;
    this.processor = processor;
    this.symbolTables = symbolTables;
    this.functions = Maps.newHashMap();
    this.effortLevel = effortLevel;
    for(Entry<Node, IRControlFlowGraph> pair : cfgs.entrySet()) {
    	String funcName = pair.getValue().getName();
    	Node funcDefNode = pair.getKey();
    	functions.put(funcName, funcDefNode);
    }
  }
  
  public static FuncInlineProcessor create(
  		RunProcessor<PathGraph> processor,
      Map<Node, IRControlFlowGraph> cfgs,
      Map<File, CSymbolTable> symbolTables) {
  	int effortLevel = Integer.MAX_VALUE;
  	if(Preferences.isSet(Preferences.OPTION_FUNC_INLINE))
  		effortLevel = Preferences.getInt(Preferences.OPTION_FUNC_INLINE);
  	return new FuncInlineProcessor(processor, cfgs, symbolTables, effortLevel);
  }
  
  public PathGraph processFunctionCall(PathGraph graph)
  		throws RunProcessorException {
    return processFuncCallWithEffortLevel(graph, 0);
	}
	
	public PathGraph processFunctionCall(PathGraph graph, 
			Iterable<Position> positions) throws RunProcessorException {
		Multimap<Pair<Integer, Integer>, Pair<CallPoint, Boolean>> callPosMap = 
				buildCallPosMap(positions);
		return processFuncCallWithEffortLevel(graph, callPosMap, 0);
	}
	
	PathGraph processFuncCallWithEffortLevelOne(PathGraph graph) throws RunProcessorException {
		
		Iterable<Path> funcPaths = pickFuncPaths(graph);
		
		if(Iterables.isEmpty(funcPaths)) return graph;
		
	  /* Function in-line for each path with function call */
	  Map<Path, PathGraph> funcPathMap = Maps.newHashMap();
	  for(Path keyPath : funcPaths) {
	    PathGraph funcGraph = functionInlinePath(keyPath);
	    funcPathMap.put(keyPath, funcGraph);
	  }
	
	  return PathGraph.insertInlineMap(graph, funcPathMap);
	}
	
	private PathGraph processFuncCallWithEffortLevel(PathGraph graph, 
			int currLevel) throws RunProcessorException {
		if(currLevel >= effortLevel) return graph;
		
		Iterable<Path> funcPaths = pickFuncPaths(graph);
		
		if(Iterables.isEmpty(funcPaths)) return graph;
		
	  /* Function in-line for each path with function call */
	  Map<Path, PathGraph> funcPathMap = Maps.newHashMap();
	  for(Path keyPath : funcPaths) {
	    PathGraph funcGraph = functionInlinePath(keyPath);
	    PathGraph inlineFuncGraph = processFuncCallWithEffortLevel(funcGraph, currLevel+1);
	    funcPathMap.put(keyPath, inlineFuncGraph);
	  }
	
	  return PathGraph.insertInlineMap(graph, funcPathMap);
	}

	private PathGraph processFuncCallWithEffortLevel(PathGraph graph, 
			Multimap<Pair<Integer, Integer>, Pair<CallPoint, Boolean>> callPosMap, 
			int currLevel) throws RunProcessorException {
		
		if(currLevel >= effortLevel) return graph;
		Iterable<Path> funcPaths = pickFuncPaths(graph);
		
		if(Iterables.isEmpty(funcPaths)) return graph;
	  
	  /* Function in-line for each path with function call */
	  Map<Path, PathGraph> funcPathMap = Maps.newHashMap();
	  for(Path keyPath : funcPaths) {
	  	CallPoint callPos = getCallPoint(keyPath, callPosMap);
	  	PathGraph inlineGraph;
	  	if(callPos == null)	{
	  		PathGraph funcGraph = functionInlinePath(keyPath);
	  		inlineGraph = processFuncCallWithEffortLevel(funcGraph, currLevel + 1);
	  	} else {
	  		PathGraph funcGraph = functionInlinePathWithCallPos(keyPath, callPos);
	  		inlineGraph = processFuncCallWithEffortLevel(funcGraph, callPosMap, currLevel + 1);
	  	}
	    funcPathMap.put(keyPath, inlineGraph);
	  }
		
	  return PathGraph.insertInlineMap(graph, funcPathMap);
	}

	private IRControlFlowGraph getCFG(final String id) {
		IRControlFlowGraph cfg = Iterables.find(cfgs.values(), 
				new Predicate<IRControlFlowGraph>() {
			@Override
			public boolean apply(IRControlFlowGraph cfg) {
				return id.equals(cfg.getName());
			}
		});
		
		return cfg;
	}

	/** Pick function paths from <code>graph</code> */
	private Iterable<Path> pickFuncPaths(PathGraph graph) {
		Iterable<Path> funcPaths = Iterables.filter(graph.getPathSet(), 
				new Predicate<Path>(){
			@Override
			public boolean apply(Path currPath) {
				return Iterables.any(currPath.getStmts(), new Predicate<IRStatement>(){
					@Override
					public boolean apply(IRStatement stmt) {
				    if(stmt.hasProperty(Identifiers.STMTFUNC)) {
				    	String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
				    	return isDefinedFunction(funcName);
				    }
				    
				    if(stmt.hasProperty(Identifiers.STMTFUNCASSIGN)) {
				    	String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
				    	return isDefinedFunction(funcName);
				    }
				    
				    return false;
					}
				});			
			}
		});
		
		return funcPaths;
	}
  
	/** Check if function <code>funcName</code> is declared */
  private boolean isDefinedFunction(String funcName) {
  	if(functions.containsKey(funcName)) {
  		return functions.get(funcName) != null;
    }
    return false;
  }
  
  /** 
   * Analyze the <code>positions</code>, to build a table from
   * location (line, column) to the collection of call point.
   * 
   * If a call point is declared nested under a loop point with
   * iteration times larger than one. Thus, we should create a 
   * collection of the call point with equal size as the iteration
   * times. In order to let multiple function call or assignment
   * function call statements after loop unrolling to pull them.
   * 
   * The collection of call point is maintained via a queue, to
   * make sure FIFO order.
   * 
   * Note that, the default function pointer column value is zero.
   * If multiple different function calls (may have same function
   * name), users needs to differentiate them via the column value
   * of the call point.
   */
  private Multimap<Pair<Integer, Integer>, Pair<CallPoint, Boolean>> buildCallPosMap(
  		Iterable<Position> positions) {
		Preconditions.checkNotNull(positions);
		Preconditions.checkArgument(!Iterables.isEmpty(positions));
		
		Collection<Position> callPositions = collectCallPositions(positions);
		
  	Multimap<Pair<Integer, Integer>, Pair<CallPoint, Boolean>> map = HashMultimap.create();
  	for(Position pos : callPositions) {
  		int line = pos.getLine();
  		for(CallPoint callPos : pos.getFunctions()) {
  			int col = callPos.getColumn().intValue();
  			Pair<Integer, Integer> location = Pair.of(line, col);
  			map.put(location, Pair.of(callPos, false));
  		}
  	}
  	
  	return map;
  }
  
  private Collection<Position> collectCallPositions(Iterable<Position> positions) {
  	Collection<Position> callPos = Lists.newArrayList();
  	for(Position pos : positions) {
  		if(pos.hasFunctions()) {
  			callPos.add(pos);
  			for(CallPoint funcPos : pos.getFunctions()) 
  				callPos.addAll(collectCallPositions(funcPos.getWayPoint()));
  		}
  		
  		if(pos.hasLoop()) {
  			for(LoopPoint loopPos : pos.getLoops())
  				callPos.addAll(collectCallPositions(loopPos.getWayPoint()));
  		}
  	}
  	
  	return callPos;
  }

  /** 
   * Get the graph of function with <code>funcName</code>.
   * 
   * The graph will be cloned before return it. It is used
   * to make sure the function graphs inlined into different
   * call position, are not share the same paths. It is to
   * avoid fake phi-node inside the graph -- that multiple 
   * function call paths joined at the entry path of function
   * graph. 
   * 
   * TODO: in the function based encoding, the clone is not 
   * necessary.
   */
	private PathGraph getFuncGraph(String funcName) 
      throws RunProcessorException {
    IRControlFlowGraph funcCfg = getCFG(funcName);
    
    if(!funcGraphMap.containsKey(funcCfg)) {
      PathGraph funcGraph = processor.processCfg(
      		funcCfg, Collections.<Position> emptyList());
      funcGraphMap.put(funcCfg, funcGraph);
    }
    
  	return funcGraphMap.get(funcCfg).clone();
  }
  
	/** 
	 * Get the graph of function with <code>funcName</code>, with 
	 * call point <code>func</code>.
	 * 
   * The graph will be cloned before return it. It is used
   * to make sure the function graphs inlined into different
   * call position, are not share the same paths. It is to
   * avoid fake phi-node inside the graph -- that multiple 
   * function call paths joined at the entry path of function
   * graph. 
   * 
   * TODO: in the function based encoding, the clone is not 
   * necessary.
   */
  private PathGraph getFuncGraphWithCallPos(String funcName, CallPoint func) 
      throws RunProcessorException {
    IRControlFlowGraph funcCfg = getCFG(funcName);
    List<Position> wayPoints = func.getWayPoint();    
    
    if(!funcWithCallGraphTable.contains(funcCfg, wayPoints)) {
    	PathGraph funcGraph = processor.processCfg(funcCfg, wayPoints);
    	funcWithCallGraphTable.put(funcCfg, wayPoints, funcGraph);
    }
    
    return funcWithCallGraphTable.get(funcCfg, wayPoints).clone();
  }
  
  /**
	 * Get the call point for <code>stmt</code> from <code>
	 * callPosTable</code>. The call point is found via the
	 * line# and col# of the source node of <code>stmt</code>.
	 * 
	 * Note that if cannot find it via <code>(line#, col#)</code>,
	 * we just find it via <code>(line#, 0)</code>. Since the user 
	 * may not specify the col# whose default value is zero.
	 * 
	 * If such a call point is found, we just pull it out from the
	 * queue in <code>callPosTable</code>, by make sure the call
	 * point is used by FIFO order.
	 * 
	 * @param stmt
	 * @param callPosTable
	 * @return <code>null</code> if no corresponding call point
	 * is found for <code>stmt</code>
	 */
	private CallPoint getCallPoint(final Path funcPath, 
			Multimap<Pair<Integer, Integer>, Pair<CallPoint, Boolean>> callPosMap) {
		Preconditions.checkArgument(funcPath.isFuncPath());
		IRStatement stmt = funcPath.getStmt(0);
		assert(stmt.getSourceNode() != null);
		assert(stmt.hasProperty(Identifiers.FUNCNAME));
		
		Node srcNode = stmt.getSourceNode();
		int srcLine = srcNode.getLocation().line;
		int srcCol = srcNode.getLocation().column;
		final String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
		
		Pair<Integer, Integer> location = Pair.of(srcLine, srcCol);
		
		if(callPosMap.containsKey(location)) { // The exact position
			Collection<Pair<CallPoint, Boolean>> pairs =
					callPosMap.get(location);
			assert(pairs.size() == 1);
			Pair<CallPoint, Boolean> pair = pairs.iterator().next();
			CallPoint callPos = pair.fst();
			assert(callPos.getFuncName().equals(funcName));
			
			Pair<CallPoint, Boolean> pairPrime = Pair.of(callPos, true);
			callPosMap.remove(location, pair);
			callPosMap.put(location, pairPrime);
			
			return callPos;
		}
		
		Pair<Integer, Integer> defaultLoc = Pair.of(srcLine, 0);
		
		if(callPosMap.containsKey(defaultLoc)) {			
			Iterable<Pair<CallPoint, Boolean>> funcPair = 
					Iterables.filter(callPosMap.get(defaultLoc), 
					new Predicate<Pair<CallPoint, Boolean>>(){
				@Override
				public boolean apply(Pair<CallPoint, Boolean> pair) {
					return pair.fst().getFuncName().equals(funcName);
				}
			});
			
			if(Iterables.isEmpty(funcPair)) return null;
			
			Pair<CallPoint, Boolean> pair = Iterables.find(funcPair, 
					new Predicate<Pair<CallPoint, Boolean>>(){
				@Override
				public boolean apply(Pair<CallPoint, Boolean> pair) {
					return !pair.snd();
				}
			}, funcPair.iterator().next());
			
			CallPoint callPos = pair.fst();
			Pair<CallPoint, Boolean> pairPrime = Pair.of(callPos, true);
			callPosMap.remove(location, pair);
			callPosMap.put(location, pairPrime);
			return callPos;
		}
		
		return null;
	}

	/**
   * Get the argument passing statements of function call nested
   * in the statement <code>stmt</code>
   * 
   * @return empty list if the function is not defined or 
   * without parameters
   */
  @SuppressWarnings("unchecked")
  private Collection<IRStatement> assignArgToParam(IRStatement stmt) {
    Preconditions.checkArgument(stmt.hasProperty(Identifiers.FUNCNAME));
    if(!stmt.hasProperty(Identifiers.ARGUMENTS)) return Collections.emptyList();
    
    String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
    assert(isDefinedFunction(funcName));
    
    Node defNode = functions.get(funcName);
    
    /* Find the parameter declare node */
    Node paramDeclare = null;
    
    for(Object o : defNode.getNode(2)) {
      if(o != null && o instanceof Node && 
      		((Node) o).hasName("FunctionDeclarator")) {
          o = ((Node) o).get(1);
      }
      
      if(o != null && o instanceof Node && 
      		((Node) o).hasName("ParameterTypeList")) {
      	paramDeclare = ((Node) o).getNode(0);
      	break;
      }
    }
    
    if(paramDeclare == null)    return Collections.emptyList();
    
    /* Pick all arguments */
    List<IRExpression> args = (List<IRExpression>) stmt.getProperty(Identifiers.ARGUMENTS);
    int argSize = args.size();
    
    assert(paramDeclare.size() == argSize);
    
    Collection<IRStatement> assignments = Lists.newArrayListWithCapacity(argSize);
    
    /* Generate assign statement one by one */
    
    /* Pick the new scope for the function declaration */
    File file = new File(defNode.getLocation().file);
    CSymbolTable symbolTable = symbolTables.get(file);
    Scope paramScope = symbolTable.getScope(defNode);
    
    for(int i=0; i < argSize; i++) {
      Node paramNode = paramDeclare.getNode(i);
      paramNode = paramNode.getNode(1);
      /* Pointer parameter declaration */
      if(paramNode.hasName("PointerDeclarator"))
        paramNode = paramNode.getNode(1);
      
      assert(paramNode.hasName("SimpleDeclarator"));
      GNode primaryId = GNode.create("PrimaryIdentifier", paramNode.get(0));
      primaryId.setLocation(paramNode.getLocation());
      for(String label : paramNode.properties())
      	primaryId.setProperty(label, paramNode.getProperty(label));
      
      IRExpressionImpl param = CExpression.create(primaryId, paramScope);
      IRExpressionImpl arg = (IRExpressionImpl) args.get(i);
      Node argNode = arg.getSourceNode();
      Node assignNode = GNode.create("AssignmentExpression", paramNode, "=", argNode);
      assignNode.setLocation(paramNode.getLocation());
      /* FIXME: assign node has no scope, we cannot attach it with the caller scope or 
       * the callee scope. assign node also has no type attached. In fact, we do not
       * bother to analyze it.
       */
//      cAnalyzer.analyze(assignNode);     
      Statement assign = Statement.assign(assignNode, param, arg);
      assignments.add(assign);
    }    
    return assignments; 
  }
  
  /**
   * Build function in-line graph for assign statement of function call 
   * <code>stmt</code>
   * 0) ent statement
   * 1) arguments passing 
	 * 2) graph built from the function declaration node.
	 * 3) return statement replacement
	 * 4) ret statement
   */
  private PathGraph inlineAssignFuncCallGraph(
  		IRStatement stmt) throws RunProcessorException {
  	Preconditions.checkArgument(stmt.hasProperty(Identifiers.STMTFUNCASSIGN));
    Preconditions.checkArgument(stmt.hasProperty(Identifiers.FUNCNAME));
  	Preconditions.checkArgument(stmt.getType().equals(StatementType.ASSIGN));
  	
    String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
  	
    if(!isDefinedFunction(funcName))	{
    	IOUtils.debug().pln("Function " + funcName + " is only declared but not yet implemented.");
    	Path path = Path.create(stmt);
    	return PathGraph.createSingleton(path);
    }
    
    PathGraph funcGraph = getFuncGraph(funcName);
    
    /* insert the assign argument to parameter statement into the funcGraph,
     * after declaration statements
     */
    Collection<IRStatement> paramPassStmts = assignArgToParam(stmt);
    if(!paramPassStmts.isEmpty())
    	funcGraph = PathGraph.insertParamArgAssignStmts(funcGraph, paramPassStmts);
    
    /* Append assign statement to all the return statements. */
    funcGraph = PathGraph.appendReturnStmt(funcGraph, stmt);
    
    return funcGraph;
  }
  
  /**
   * Build function in-line graph for assign statement of function call 
   * <code>stmt</code> with call point <code>func</code>
   * 0) ent statement
   * 1) arguments passing 
	 * 2) graph built from the function declaration node.
	 * 3) return statement replacement
	 * 4) ret statement
   */
	private PathGraph inlineAssignFuncCallGraphWithCallPos(
			IRStatement stmt, 
			CallPoint func) throws RunProcessorException {
  	Preconditions.checkArgument(stmt.hasProperty(Identifiers.STMTFUNCASSIGN));
    Preconditions.checkArgument(stmt.hasProperty(Identifiers.FUNCNAME));
  	Preconditions.checkArgument(stmt.getType().equals(StatementType.ASSIGN));
  	
	  String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
		
	  if(!isDefinedFunction(funcName))	{
	  	IOUtils.debug().pln("Function " + funcName + " is only declared but not yet implemented.");
	  	return PathGraph.createSingleton(Path.create(stmt));
	  }
	  
	  PathGraph funcGraph = getFuncGraphWithCallPos(funcName, func);
	  
  	/* add the assign argument to parameter statement */
	  Collection<IRStatement> paramPassStmts = assignArgToParam(stmt);
	  if(!paramPassStmts.isEmpty())
	  	funcGraph = PathGraph.insertParamArgAssignStmts(funcGraph, paramPassStmts);
	  
	  /* replace all the return statements. */
	  funcGraph = PathGraph.appendReturnStmt(funcGraph, stmt);
	  
	  return funcGraph;
	}

  /**
   * Build function in-line graph for call statement of function call 
   * <code>stmt</code>
   * 0) ent statement
   * 1) arguments passing 
	 * 2) graph built from the function declaration node.
	 * 3) ret statement
   */
  private PathGraph inlineFuncCallGraph(IRStatement stmt) 
  		throws RunProcessorException {
  	Preconditions.checkArgument(stmt.hasProperty(Identifiers.STMTFUNC));
    Preconditions.checkArgument(stmt.hasProperty(Identifiers.FUNCNAME));
    Preconditions.checkArgument(stmt.getType().equals(StatementType.CALL));
    
    String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
    
    if(!isDefinedFunction(funcName))	{
    	IOUtils.debug().pln("Function " + funcName + " is only declared but not yet implemented.");
    	return PathGraph.createSingleton(Path.create(stmt));
    }
    
    PathGraph funcGraph = getFuncGraph(funcName);
  	
    Collection<IRStatement> paramPassStmts = assignArgToParam( stmt);
    if(!paramPassStmts.isEmpty())
    	funcGraph = PathGraph.insertParamArgAssignStmts(funcGraph, paramPassStmts);
    
    return funcGraph;
  }

  /**
   * Build function in-line graph for call statement of function call 
   * <code>stmt</code> with call point <code>func</code>
   * 0) ent statement
   * 1) arguments passing 
	 * 2) graph built from the function declaration node
	 * 3) ret statement
   */
  private PathGraph inlineFuncCallGraphWithCallPos(
  		IRStatement stmt, CallPoint func) throws RunProcessorException {
  	Preconditions.checkArgument(stmt.hasProperty(Identifiers.STMTFUNC));
    Preconditions.checkArgument(stmt.hasProperty(Identifiers.FUNCNAME));
    Preconditions.checkArgument(stmt.getType().equals(StatementType.CALL));
    
    String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
    
    if(!isDefinedFunction(funcName))	{
    	IOUtils.debug().pln("Function " + funcName + " is only declared but not yet implemented.");
    	return PathGraph.createSingleton(Path.create(stmt));
    }
    
    PathGraph funcGraph = getFuncGraphWithCallPos(funcName, func);
    
    Collection<IRStatement> paramPassStmts = assignArgToParam(stmt);
    if(!paramPassStmts.isEmpty()) {
    	funcGraph = PathGraph.insertParamArgAssignStmts(funcGraph, paramPassStmts);
    }
    
    return funcGraph;
  }
  
  /** Build function in-lined graph for <code>path</code> */
  private PathGraph functionInlinePath(Path path) 
      throws RunProcessorException {
    Preconditions.checkArgument(path.isFuncPath());
    
    IRStatement stmt = path.getStmt(0);
    if(stmt.hasProperty(Identifiers.STMTFUNCASSIGN))
    	return inlineAssignFuncCallGraph(stmt);
    else
    	return inlineFuncCallGraph(stmt);
  }
 
  /** 
   * Build function in-line graph for <code>path</code> with 
   * the <code>callPosTable</code>
   */
  private PathGraph functionInlinePathWithCallPos(
  		Path path, 
  		CallPoint callPos) throws RunProcessorException {
  	Preconditions.checkArgument(path.isFuncPath());
  	Preconditions.checkNotNull(callPos);
  	
  	IRStatement stmt = path.getStmt(0);
  	if(stmt.hasProperty(Identifiers.STMTFUNCASSIGN))
			return inlineAssignFuncCallGraphWithCallPos(stmt, callPos);
		else
    	return inlineFuncCallGraphWithCallPos(stmt, callPos);
  }	
}
