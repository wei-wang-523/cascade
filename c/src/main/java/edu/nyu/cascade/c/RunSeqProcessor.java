package edu.nyu.cascade.c;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.util.*;
import java.util.Map.Entry;

import xtc.parser.*;
import xtc.tree.*;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.*;

import edu.nyu.cascade.c.CAnalyzer;
import edu.nyu.cascade.c.CSpecParser;
import edu.nyu.cascade.c.mode.Mode;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.control.*;
import edu.nyu.cascade.control.jaxb.InsertionType;
import edu.nyu.cascade.control.jaxb.Position.Command;
import edu.nyu.cascade.ir.*;
import edu.nyu.cascade.ir.IRStatement.StatementType;
import edu.nyu.cascade.ir.expr.*;
import edu.nyu.cascade.ir.impl.*;
import edu.nyu.cascade.ir.path.SimplePathEncoding;
import edu.nyu.cascade.util.*;

/**
 * A processor for control file runs (i.e., non-looping paths annotated
 * through the program).
 */
class RunSeqProcessor implements RunProcessor<List<IRStatement>> {
  
  public RunSeqProcessor(
  		Mode mode,
  		Map<File, CSymbolTable> symbolTables,
      Map<Node, IRControlFlowGraph> cfgs, 
      CAnalyzer cAnalyzer)
      throws RunProcessorException {
    this.symbolTables = symbolTables;
    this.cfgs = cfgs;
    this.cAnalyzer = cAnalyzer;
    this.mode = mode;
    
    CExpressionEncoder encoder = CExpressionEncoder.create(mode);
    
    pathEncoder = PathSeqEncoder.create(SimplePathEncoding.create(encoder));
  }
  
  private final Map<File, CSymbolTable> symbolTables;
  private final Map<Node, IRControlFlowGraph> cfgs;
  private final CAnalyzer cAnalyzer;
  private final PathSeqEncoder pathEncoder;
  private final Mode mode;

  @Override
  public boolean process(Run run) throws RunProcessorException {
    try {
    	
      /* Build the graph for this run */
      Position startPos = run.getStartPosition();
      Position endPos = run.getEndPosition();
      IRControlFlowGraph cfg = getCFGForLocation(startPos);
      
      Collection<Position> waypoints = new ImmutableList.Builder<Position>().
      		add(startPos).addAll(run.getWayPoints()).add(endPos).build();
      List<IRStatement> path = processCfg(cfg, waypoints);
      
      Collection<IRStatement> globalStmts = getGlobalStatements();
    	path.addAll(0, globalStmts);
      
      if (IOUtils.debugEnabled()) {
        IOUtils.debug().pln("Complete path for run...");
        for (IRStatement stmt : path) {
          IOUtils
              .debug()
              .pln(stmt.getLocation() + " " + stmt.toString())
              .flush();
        }
      }      
      
      PreProcessor<?> preprocessor = null;
      
      if(mode.hasPreprocessor()) {
        File file = run.getStartPosition().getFile();
        CSymbolTable symbolTable = symbolTables.get(file);
        preprocessor = mode.buildPreprocessor(symbolTable);
      }
      
      pathEncoder.encode(preprocessor, path);

      if (pathEncoder.runIsValid() && !pathEncoder.runIsFeasible()) {
        IOUtils.err().println("WARNING: path assumptions are unsatisfiable");
      }
      
      return pathEncoder.runIsValid();
    } catch (PathFactoryException e) {
      throw new RunProcessorException(e);
    }
  }

  @Override
	public List<IRStatement> processCfg(IRControlFlowGraph cfg, Collection<Position> waypoints) 
	        throws RunProcessorException {   
    File file = new File(cfg.getSourceNode().getLocation().file);
    CSymbolTable symbolTable = symbolTables.get(file);   
    Scope oldScope = symbolTable.getCurrentScope();
    symbolTable.enterScope(cfg);
    
    List<IRStatement> path = processRunBtwnBlocks(
    		cfg.getEntry(), cfg.getExit(), waypoints, cfg, symbolTable);
	  
	  symbolTable.setScope(oldScope);
	  
	  return path;
	}
  
	@Override
  public boolean processReachability(IRControlFlowGraph mainCfg, String label)
      throws RunProcessorException {
	  throw new UnsupportedOperationException();
  }
	
	@Override
  public Table<Integer, Integer, Boolean> processReachabilityIncremental(
  		IRControlFlowGraph mainCfg, String label)
  				throws RunProcessorException {
	  throw new UnsupportedOperationException();
  }

	@Override
	public void enableFeasibilityChecking() {
	  pathEncoder.setFeasibilityChecking(true);
	}
	
	@Override
	public List<IRStatement> processRunBtwnBlocks(
			IRBasicBlock startBlock, 
			IRBasicBlock endBlock, 
			Collection<Position> waypoints,
			IRControlFlowGraph cfg,
			CSymbolTable symbolTable) 
					throws RunProcessorException {
    
    Collection<Position> unrollWayPoints = Collections.emptyList();
    if(waypoints != null)
    	unrollWayPoints = loopPointsUnroll(cfg, waypoints);
    
    List<IRStatement> path = Lists.newArrayList();
    
    IRBasicBlock block = startBlock;
    
    for(Position pos : unrollWayPoints) {
    	if (block == null)      break;
    	IOUtils.debug().pln("<wayPoint> " + pos.toString()).flush();
    	
    	Pair<? extends IRBasicBlock, ? extends IRBasicBlock> pair = 
    			cfg.splitAt(pos, pos.hasLoop(), 
    					InsertionType.BEFORE.equals(pos.getInsertionType()));
    	
    	IRBasicBlock target = pair.fst();
    	
    	List<IRStatement> wayPath;
    	if(target != null)
    		wayPath = buildPathToBlock(cfg, block, target);
    	else
    		wayPath = Collections.emptyList();
    	
    	block = pair.snd();
    	
    	Scope currScope = symbolTable.getCurrentScope();
    	if(block.getScope() != null)   symbolTable.setScope(block.getScope());
    	
    	if(pos.hasInvariant()) {
    		Collection<IRStatement> invPath = processInvariant(cfg, pos, symbolTable);
    		wayPath.addAll(invPath);
    	}
        
    	Collection<IRStatement> posPath = processPosition(pos, symbolTable);
    	if(posPath != null) wayPath.addAll(posPath);
    	symbolTable.setScope(currScope);
        
    	path.addAll(wayPath);
    }
    
    // End position
    if (block == null)
      throw new RunProcessorException("Function ended before end of run.");
    
    Collection<IRStatement> endPath = buildPathToBlock(cfg, block, endBlock); 
    
    if(endPath != null) path.addAll(endPath);
    
    Iterable<Position> funcCallPoints = Iterables.filter(unrollWayPoints, 
    		new Predicate<Position>(){
					@Override
          public boolean apply(Position waypoint) {
	          return waypoint.hasFunctions();
          }
    });
	  
	  if(Iterables.isEmpty(funcCallPoints))
	  	path = functionInline(symbolTable, path);
	  else
	  	path = functionInlineWithCallPos(symbolTable, path, funcCallPoints);
	  
	  return path;
	}

	/** Incorporate the command for the given position into the given path. */
  private Collection<IRStatement> processPosition(Position position, CSymbolTable symbolTable) 
      throws RunProcessorException {
    Preconditions.checkNotNull(position);
    Collection<IRStatement> path = Lists.newArrayList();
    List<Command> cmds = position.getCommands();
    for(Command cmd : cmds) {
      try {
        String funName = cmd.getCascadeFunction();
        CSpecParser funParser = new CSpecParser(new StringReader(funName),
            position.getFile().getPath());
        Result funResult = funParser.pCSpecExpression(0);
        Node fun = (Node) funParser.value(funResult);
        Location loc = new Location(position.getFile().getPath(), position.getLine(), 0);
        fun.setLocation(loc);
      
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
          CExpression argExpr = CfgBuilder.analyze(symbolTable, cAnalyzer, spec);
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
    
    if(path.isEmpty())  return null;
    
    return path;
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
  
  private List<IRStatement> buildPathToBlock(IRControlFlowGraph cfg,
      IRBasicBlock start, IRBasicBlock target) 
          throws RunProcessorException {
  	Preconditions.checkNotNull(start);
  	Preconditions.checkNotNull(target);
  	
    List<IRStatement> path = Lists.newArrayList();
    /* Find the shortest path from block to target, using a backwards
     * breadth-first search. pathMap will associate each block with its
     * "next hop" in the shortest path.
     */
    Map<IRBasicBlock, IREdge<?>> pathMap = Maps.newHashMap();
    Set<IRBasicBlock> visited = Sets.newHashSet();
    Deque<IRBasicBlock> queue = Queues.newArrayDeque();
    
    /* For finding a loop from start to start/target. Add incoming 
     * edges and their source nodes into pathMap and visited set
     * before entering into while-loop. It means to avoid labeling
     * start as visited node.
     */
    if(start.equals(target) && 
        (start.getType().equals(IRBasicBlock.Type.LOOP) || 
            (start.getType()).equals(IRBasicBlock.Type.SWITCH))) {
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
      /* The two blocks aren't connected! */
      IOUtils.err().println("No path found.");
      throw new RunProcessorException("Invalid run");
    }

    /* Add statements along the shortest path */
    IRBasicBlock u = start;
    IOUtils.debug().pln("Shortest path:").incr().flush();
    
    /* For finding a loop from start to start/target. Add incoming 
     * edges and their source nodes into pathMap and visited set
     * before entering into while-loop. It means to avoid labeling
     * start as visited node.
     */
    if((start.equals(target) && 
        (start.getType().equals(IRBasicBlock.Type.LOOP) || 
            (start.getType()).equals(IRBasicBlock.Type.SWITCH)))) {
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
        path.addAll(buildPathToBlock(cfg, u, u));
        iterTimes--;
      }
      path.addAll(u.getStatements());
      IREdge<?> e = pathMap.get(u);
      assert (e != null);
      addEdgeToPath(path, e);
      u = e.getTarget();
    }
    
    path.addAll(target.getStatements());
    IOUtils.debug().decr().flush();

    return path;
  }
  
  private void addEdgeToPath(List<IRStatement> path, IREdge<?> e) {
    if (e.getGuard() != null) {
      path.add(Statement.assumeStmt(e.getSourceNode(), e.getGuard()));
    }
  }

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
  
  /** Check if function <code>funcName</code> is declared */
  private boolean isDefinedFunction(final String funcName) {
    return Iterables.any(cfgs.values(), new Predicate<IRControlFlowGraph>(){

			@Override
      public boolean apply(IRControlFlowGraph cfg) {
	      return funcName.equals(cfg.getName());
      }
    	
    });
  }
  
  private Node getFuncDefinitionNode(final String funcName) {
  	return Iterables.find(cfgs.entrySet(), new Predicate<Entry<Node, IRControlFlowGraph>>(){
			@Override
      public boolean apply(Entry<Node, IRControlFlowGraph> entry) {
	      return funcName.equals(entry.getValue().getName());
      }
  	}).getKey();
  }
  
  /** 
	 * Analyze the <code>positions</code>, to build the map from
	 * location (line, column) to call position.
	 */
	private Table<Integer, Integer, Queue<CallPoint>> buildCallPosMap(
			Iterable<Position> positions) {
		Table<Integer, Integer, Queue<CallPoint>> table = HashBasedTable.create();
		for(Position pos : positions) {
			int line = pos.getLine();
			for(CallPoint callPos : pos.getFunctions()) {
				int col = callPos.getColumn().intValue();
				Queue<CallPoint> queue = table.get(line, col);
				if(queue == null) {
					queue = Queues.newArrayDeque();
				} else {
					CallPoint callPos_ = queue.peek();
					assert(callPos_.getFuncName().equals(callPos.getFuncName()));
				}
				queue.add(callPos);
				table.put(line, col, queue);
			}
		}
		return table;
	}

	/** Get the call point for <code>stmt</code> from <code>funcs</code> */
	private CallPoint getCallPoint(final IRStatement stmt, 
			Table<Integer, Integer, Queue<CallPoint>> callPosMap) {
		Preconditions.checkNotNull(stmt.getSourceNode());
		Node srcNode = stmt.getSourceNode();
		int srcLine = srcNode.getLocation().line;
		int srcCol = srcNode.getLocation().column;
		
		if(!callPosMap.containsRow(srcLine)) return null;
		
		if(callPosMap.contains(srcLine, srcCol))	{
			CallPoint callPos = callPosMap.get(srcLine, srcCol).poll();
			String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
			String funcName_ = callPos.getFuncName();
			assert(funcName.equals(funcName_));
			return callPos;
		} else {
			Queue<CallPoint> callPoses = callPosMap.get(srcLine, 0);
			CallPoint callPos = callPoses.peek();
			String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
			String funcName_ = callPos.getFuncName();
			if(funcName.equals(funcName_)) return callPoses.poll();
			return null;
		}
	}

	/**
	 * Get the argument passing statements of function call.
	 * @return Argument passing statements, empty list
	 * if the function is not defined or without parameters
	 */
	@SuppressWarnings("unchecked")
	private Collection<IRStatement> assignArgToParam(CSymbolTable symbolTable, 
			IRStatement stmt) {
	  Preconditions.checkArgument(stmt.hasProperty(Identifiers.FUNCNAME));
	  String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
	  Preconditions.checkArgument(isDefinedFunction(funcName));
	  
	  Node defNode = getFuncDefinitionNode(funcName);
	  
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
	  
	  if(!stmt.hasProperty(Identifiers.ARGUMENTS)) return Collections.emptyList();
	  
	  /* Pick all arguments */
	  List<IRExpression> args = (List<IRExpression>) stmt.getProperty(Identifiers.ARGUMENTS);
	  int argSize = args.size();
	  
	  assert(paramDeclare.size() == argSize);
	  
	  Collection<IRStatement> assignments = Lists.newArrayListWithCapacity(argSize);
	  
	  /* Generate assign statement one by one */
	  /* Pick the new scope for the function declaration */
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
//	    if(argNode.hasName("FunctionCall") 
//	    		&& argNode.getNode(0).getString(0).equals((ReservedFunction.ANNO_NONDET))) {
//	    	Statement havoc = Statement.havoc(argNode, param);
//	    	assignments.add(havoc);
//	    } else {
	      Node assignNode = GNode.create("AssignmentExpression", paramNode, "=", argNode);
	      assignNode.setLocation(paramNode.getLocation());
//	      Type type = cAnalyzer.processAssignment(false, "assignment", 
//	      		assignNode, CType.getType(paramNode), CType.getType(argNode));
//	      cAnalyzer.mark(assignNode, type);   
	      Statement assign = Statement.assign(assignNode, param, arg);
	      assignments.add(assign);
//	    }
	  }    
	  return assignments; 
	}

	/** 
   * Collect a list Statement from function body, func is the function
   * section in the control file, might with loop position and way points
   * nested inside.
   */
  private List<IRStatement> collectStmtFromFunction(
  		CSymbolTable symbolTable, 
  		String funcName, 
  		CallPoint func) 
  				throws RunProcessorException {
  	Preconditions.checkArgument(isDefinedFunction(funcName));
  	Node bestNode = getFuncDefinitionNode(funcName);
    
    IRControlFlowGraph funcCfg = cfgs.get(bestNode); 
    IRBasicBlock funcStart = funcCfg.getEntry();
    IRBasicBlock funcEnd = funcCfg.getExit();
    List<Position> waypoints = null;
    if(func != null) waypoints = func.getWayPoint();
    return processRunBtwnBlocks(funcStart, funcEnd, waypoints, funcCfg, symbolTable);
  }
  
  /** Replace the last return statement as assign statement. */
  private IRStatement replaceReturnStmt(CSymbolTable symbolTable, IRStatement returnStmt, IRStatement assignStmt) {
    Preconditions.checkArgument(returnStmt.getType().equals(StatementType.RETURN));
    IRExpressionImpl lExpr = (IRExpressionImpl) assignStmt.getOperand(0);
    IRExpressionImpl rExpr = (IRExpressionImpl) returnStmt.getOperand(0);
    GNode assignNode = GNode.create("AssignmentExpression", 
        lExpr.getSourceNode(), "=", rExpr.getSourceNode());
    assignNode.setLocation(assignStmt.getSourceNode().getLocation());
    IRStatement assignResult = Statement.assign(assignNode, lExpr, rExpr);
    return assignResult;
  }

	private List<IRStatement> functionInline(
			CSymbolTable symbolTable, 
  		List<IRStatement> path) 
  				throws RunProcessorException {
    Preconditions.checkNotNull(path);
    IOUtils.debug().pln("Checking path...");
    
    /* The map from index inside path to the collection of statements
     * collected from function inline the statement at specific index. */
    Map<Integer, Collection<IRStatement>> funcInlineMap = Maps.newHashMap();
    
    for(int i = 0; i < path.size(); i++) {
    	IRStatement stmt = path.get(i);
    	if(stmt.hasProperty(Identifiers.STMTFUNC)) {
    		Collection<IRStatement> funcInlineStmts = inlineFuncCall(symbolTable, stmt);
    		funcInlineMap.put(i, funcInlineStmts);
    		continue;
    	}
    	
    	if(stmt.hasProperty(Identifiers.STMTFUNCASSIGN)) {
    		Collection<IRStatement> funcInlineStmts = inlineAssignFuncCall(symbolTable, stmt);
    		funcInlineMap.put(i, funcInlineStmts);
    		continue;
    	}
    }
    
    List<IRStatement> resPath = Lists.newArrayList();
    for(int i = 0; i < path.size(); i++) {
    	if(!funcInlineMap.containsKey(i)) {
    		resPath.add(path.get(i)); continue;
    	}
    	resPath.addAll(funcInlineMap.get(i));
    }
    
    return resPath;
  }
  
  private List<IRStatement> functionInlineWithCallPos(
  		CSymbolTable symbolTable, 
  		List<IRStatement> path, 
  		Iterable<Position> funcCallPoints) 
  				throws RunProcessorException {
    Preconditions.checkNotNull(path);
    IOUtils.debug().pln("Checking path...");
    
    Table<Integer, Integer, Queue<CallPoint>> callPosTable = buildCallPosMap(funcCallPoints);
    
    /* The map from index inside path to the collection of statements
     * collected from function inline the statement at specific index. */
    Map<Integer, Collection<IRStatement>> funcInlineMap = Maps.newHashMap();
    
    for(int i = 0; i < path.size(); i++) {
    	IRStatement stmt = path.get(i);
    	if(stmt.hasProperty(Identifiers.STMTFUNC)) {
    		CallPoint callPos = getCallPoint(stmt, callPosTable);
    		Collection<IRStatement> funcInlineStmts = null;
    		if(callPos == null)
    			funcInlineStmts = inlineFuncCall(symbolTable, stmt);
    		else
    			funcInlineStmts = inlineFuncCallWithCallPos(symbolTable, stmt, callPos);
    		funcInlineMap.put(i, funcInlineStmts);
    		continue;
    	}
    	
    	if(stmt.hasProperty(Identifiers.STMTFUNCASSIGN)) {
    		CallPoint callPos = getCallPoint(stmt, callPosTable);
    		Collection<IRStatement> funcInlineStmts = null;
    		if(callPos == null)
    			funcInlineStmts = inlineAssignFuncCall(symbolTable, stmt);
    		else
    			funcInlineStmts = inlineAssignFuncCallWithCallPos(symbolTable, stmt, callPos);
    		funcInlineMap.put(i, funcInlineStmts);
    		continue;
    	}
    }
    
    List<IRStatement> resPath = Lists.newArrayList();
    for(int i = 0; i < path.size(); i++) {
    	if(!funcInlineMap.containsKey(i)) {
    		resPath.add(path.get(i)); continue;
    	}
    	resPath.addAll(funcInlineMap.get(i));
    }
    
    return resPath;
  }
  
  private Collection<IRStatement> inlineAssignFuncCall(
  		CSymbolTable symbolTable,
	    IRStatement stmt) 
	    		throws RunProcessorException {
		Preconditions.checkArgument(stmt.getType().equals(StatementType.ASSIGN));
		
	  String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
		
	  if(!isDefinedFunction(funcName))	{
	  	IOUtils.debug().pln("Function " + funcName + " is only declared but not yet implemented.");
	  	return Collections.singletonList(stmt);
	  }
	  
  	List<IRStatement> funcStmts = collectStmtFromFunction(symbolTable, funcName, null);
  	Collection<IRStatement> argAssignStmts = assignArgToParam(symbolTable, stmt);
  	
 	 	/* Pick the declaration statements */
  	Iterator<IRStatement> argAssignItr = argAssignStmts.iterator();
  	List<IRStatement> resStmts = Lists.newArrayList();
  	
  	for(IRStatement currStmt : funcStmts) {
			resStmts.add(currStmt);
  		if(currStmt.getType().equals(StatementType.DECLARE)) {
  			if(argAssignItr.hasNext())
  				resStmts.add(argAssignItr.next());
			}
  	}
  	
  	for(int i = resStmts.size() - 1; i >= 0; i--) {
  		IRStatement currStmt = resStmts.get(i);
  		if(currStmt.getType().equals(StatementType.RETURN)) {
  			IRStatement assignResult = replaceReturnStmt(symbolTable, currStmt, stmt);
  			resStmts.set(i, assignResult);
  			break;
  		}
  	}
  	
	  return resStmts;
	}

	private Collection<IRStatement> inlineAssignFuncCallWithCallPos(
      CSymbolTable symbolTable, 
      IRStatement stmt, 
      CallPoint callPos) 
      		throws RunProcessorException {
  	Preconditions.checkArgument(stmt.getType().equals(StatementType.ASSIGN));
  	
    String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
  	
    if(!isDefinedFunction(funcName))	{
    	IOUtils.debug().pln("Function " + funcName + " is only declared but not yet implemented.");
    	return Collections.singletonList(stmt);
    }
    
  	List<IRStatement> funcStmts = collectStmtFromFunction(symbolTable, funcName, callPos);
  	Collection<IRStatement> argAssignStmts = assignArgToParam(symbolTable, stmt);
  	
 	 	/* Pick the declaration statements */
  	Iterator<IRStatement> argAssignItr = argAssignStmts.iterator();
  	List<IRStatement> resStmts = Lists.newArrayList();
  	
  	for(IRStatement currStmt : funcStmts) {
			resStmts.add(currStmt);
  		if(currStmt.getType().equals(StatementType.DECLARE)) {
  			if(argAssignItr.hasNext())
  				resStmts.add(argAssignItr.next());
			}
  	}
  	
  	for(int i = resStmts.size() - 1; i >= 0; i--) {
  		IRStatement currStmt = resStmts.get(i);
  		if(currStmt.getType().equals(StatementType.RETURN)) {
  			IRStatement assignResult = replaceReturnStmt(symbolTable, currStmt, stmt);
  			resStmts.set(i, assignResult);
  			break;
  		}
  	}
  	
	  return resStmts;
  }

	private Collection<IRStatement> inlineFuncCallWithCallPos(
			CSymbolTable symbolTable,
      IRStatement stmt, 
      CallPoint callPos) 
      		throws RunProcessorException {
    Preconditions.checkArgument(stmt.getType().equals(StatementType.CALL));
    
    String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
    
    if(!isDefinedFunction(funcName))	{
    	IOUtils.debug().pln("Function " + funcName + " is only declared but not yet implemented.");
    	return Collections.singletonList(stmt);
    }
    
  	List<IRStatement> funcStmts = collectStmtFromFunction(symbolTable, funcName, callPos);
  	Collection<IRStatement> argAssignStmts = assignArgToParam(symbolTable, stmt);
  	
 	 	/* Pick the declaration statements */
  	Iterator<IRStatement> argAssignItr = argAssignStmts.iterator();
  	List<IRStatement> resStmts = Lists.newArrayList();
  	
  	for(IRStatement currStmt : funcStmts) {
			resStmts.add(currStmt);
  		if(currStmt.getType().equals(StatementType.DECLARE)) {
  			if(argAssignItr.hasNext())
  				resStmts.add(argAssignItr.next());
			}
  	}
  	
	  return resStmts;
  }

	private Collection<IRStatement> inlineFuncCall(
			CSymbolTable symbolTable,
	    IRStatement stmt) 
	    		throws RunProcessorException {
    Preconditions.checkArgument(stmt.getType().equals(StatementType.CALL));
    
    String funcName = (String) stmt.getProperty(Identifiers.FUNCNAME);
    
    if(!isDefinedFunction(funcName))	{
    	IOUtils.debug().pln("Function " + funcName + " is only declared but not yet implemented.");
    	return Collections.singletonList(stmt);
    }
    
  	List<IRStatement> funcStmts = collectStmtFromFunction(symbolTable, funcName, null);

  	Collection<IRStatement> argAssignStmts = assignArgToParam(symbolTable, stmt);
  	
 	 	/* Pick the declaration statements */
  	Iterator<IRStatement> argAssignItr = argAssignStmts.iterator();
  	List<IRStatement> resStmts = Lists.newArrayList();
  	
  	for(IRStatement currStmt : funcStmts) {
			resStmts.add(currStmt);
  		if(currStmt.getType().equals(StatementType.DECLARE)) {
  			if(argAssignItr.hasNext())
  				resStmts.add(argAssignItr.next());
			}
  	}
  	
	  return resStmts;
	}

	/** Parse the invariant of loop. */
  private Collection<IRStatement> processInvariant(
  		IRControlFlowGraph cfg, 
  		Position position, 
      CSymbolTable symbolTable) 
      		throws RunProcessorException {
  	
    try {
      CSpecParser specParser = new CSpecParser(new StringReader(position.getInvariant()),
          position.getFile().getPath());
      Result specResults = specParser.pCSpecExpression(0);
      Node spec = (Node) specParser.value(specResults);
      Location loc = new Location(position.getFile().getPath(), position.getLine(), 0);
      spec.setLocation(loc);
      
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
      
      /* FIXME: CVC4 has incremental support problem, multiple queries are not supported
       * well. If this assertion statement is added, will have invalid memory access inside
       * CVC4
       */
      IRStatement assertStmt = Statement.assertStmt(spec, argExpr);
      IRStatement assumeStmt = Statement.assumeStmt(spec, argExpr);
      
      // Pick all statements from the loop body
      List<Position> wayPoints = position.getLoops().iterator().next().getWayPoint();
      
      IRBasicBlock loopBlock = cfg.bestBlockForPosition(position, position.hasLoop());
      List<IRStatement> loopPath = processRunBtwnBlocks(loopBlock, loopBlock, wayPoints, cfg, symbolTable);
      
      // Process havoc statements and declaration statements
      Iterable<IRStatement> havocDeclStmts = liftHavocDeclStatements(loopPath);
      Iterable<IRStatement> remainStmts = removeDeclarations(loopPath);
      
      return new ImmutableList.Builder<IRStatement>().add(assertStmt)
      		.addAll(havocDeclStmts)
      		.add(assumeStmt)
      		.addAll(remainStmts)
      		.add(assertStmt).build();
      
    } catch (IOException e) {
      throw new RunProcessorException("Specification parse failure", e);
    } catch (ParseException e) {
      throw new RunProcessorException("Specification parse failure", e);
    }
  }
  
  private Collection<Position> loopPointsUnroll(IRControlFlowGraph cfg, Collection<Position> waypoints) 
      throws RunProcessorException {
    Preconditions.checkNotNull(waypoints);
    Collection<Position> resWaypoints = Lists.newArrayList();
    for(Position pos : waypoints) {
      if(pos.hasLoop()) {
        /* Clear default iteration times in loop block if users 
      	 * specify iteration times in ctrl file
      	 */ 
        cfg.bestBlockForPosition(pos, pos.hasLoop()).clearIterTimes();
       
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
          // if last loop point doesn't contains wayPoint, add iteration times to hit the entry
          // block of the loop and exit
          if(lastLoopPos.getWayPoint().isEmpty()) 
            resWaypoints.add(pos);
        }
      } else {
        resWaypoints.add(pos);
      }
    }
    return resWaypoints;
  }
  
	/** Lift all the declaration statements, generate all the havoc statements */
	private Iterable<IRStatement> liftHavocDeclStatements(Collection<IRStatement> path) {
		ImmutableList.Builder<IRStatement>  builder = new ImmutableList.Builder<IRStatement>();
		
		for(IRStatement stmt : path) {
			switch(stmt.getType()) {
			case ALLOC:
			case ASSIGN:
				Statement havocStmt = Statement.havoc(stmt.getSourceNode(), stmt.getOperand(0));
				builder.add(havocStmt);
				break;
			case DECLARE:
			case HAVOC:
			case FUNC_ENT:
			case FUNC_EXIT:
				builder.add(stmt);
				break;
			default:
				break;
			}
		}
		
		return builder.build();
	}
	
	private Iterable<IRStatement> removeDeclarations(Collection<IRStatement> path) {
		return Iterables.filter(path, new Predicate<IRStatement>(){
			@Override
      public boolean apply(IRStatement stmt) {
	      return !stmt.getType().equals(IRStatement.StatementType.DECLARE);
      }
		});
	}
	
	private Collection<IRStatement> getGlobalStatements() throws RunProcessorException {
    /* Build the global graph with global variables and statements */
		for(IRControlFlowGraph cfg : cfgs.values()) {
			if(Identifiers.GLOBAL_CFG.equals(cfg.getName())) {
		    return processCfg(cfg, Collections.<Position> emptyList());
			}
		}
		
		return Collections.emptyList();
	}
}