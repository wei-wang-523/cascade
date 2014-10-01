package edu.nyu.cascade.c;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import xtc.parser.ParseException;
import xtc.parser.Result;
import xtc.tree.Location;
import xtc.tree.Node;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.base.Stopwatch;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Table;

import edu.nyu.cascade.c.CAnalyzer;
import edu.nyu.cascade.c.CSpecParser;
import edu.nyu.cascade.c.mode.Mode;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.control.Position;
import edu.nyu.cascade.control.Run;
import edu.nyu.cascade.control.jaxb.InsertionType;
import edu.nyu.cascade.control.jaxb.Position.Command;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRBasicBlock.Type;
import edu.nyu.cascade.ir.expr.PathFactoryException;
import edu.nyu.cascade.ir.impl.Statement;
import edu.nyu.cascade.ir.path.SimplePathEncoding;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;

/**
 * A processor for control file runs. It is statement-based.
 * For loop point and function call point, we handle them separately.
 * Create a loop graph for every loop point, and create a function
 * in-line graph for every path contains call statement. In-line them
 * into the original graph.
 */
class RunMergeProcessor implements RunProcessor<PathGraph> {

	private RunMergeProcessor(
  		Mode mode,
  		Map<File, CSymbolTable> symbolTables,
      Map<Node, IRControlFlowGraph> cfgs,
      CAnalyzer cAnalyzer) {
    this.symbolTables = symbolTables;
    this.cfgs = cfgs;
    this.cAnalyzer = cAnalyzer;
    this.mode = mode;
    
    CExpressionEncoder encoder = CExpressionEncoder.create(mode);
    this.pathEncoder = PathMergeEncoder.create(SimplePathEncoding.create(encoder));
    funcProcessor = FuncInlineProcessor.create(this, cfgs, symbolTables);
    loopProcessr = LoopInlineProcessor.create(this, symbolTables, cAnalyzer);
  }
  
	static RunMergeProcessor create(
  		Mode mode,
  		Map<File, CSymbolTable> symbolTables,
      Map<Node, IRControlFlowGraph> cfgs,
      CAnalyzer cAnalyzer) {
  	return new RunMergeProcessor(mode, symbolTables, cfgs, cAnalyzer);
  }
  
  private final Map<File, CSymbolTable> symbolTables;
  private final Map<Node, IRControlFlowGraph> cfgs;
  private final CAnalyzer cAnalyzer;
  private final PathMergeEncoder pathEncoder;
  private final FuncInlineProcessor funcProcessor;
  private final LoopInlineProcessor loopProcessr;
  private final Mode mode;
  private final Stopwatch timer = Stopwatch.createUnstarted();
  
  @Override
	public void enableFeasibilityChecking() {
	  pathEncoder.setFeasibilityChecking(true);
	}
  
  @Override
  public boolean process(Run run) throws RunProcessorException {
    try {
    	
      /* Pre-processing the graph */
      PreProcessor<?> preprocessor = null;
      
      if(mode.hasPreprocessor()) {
        File file = run.getStartPosition().getFile();
        CSymbolTable symbolTable = symbolTables.get(file);
        preprocessor = mode.buildPreprocessor(symbolTable);
      }
      
    	timer.start();
      
      /* Build the graph for this run */
      Position startPos = run.getStartPosition();
      Position endPos = run.getEndPosition();
      IRControlFlowGraph cfg = getCFGForLocation(startPos);
      
      Collection<Position> waypoints = new ImmutableList.Builder<Position>().
      		add(startPos).addAll(run.getWayPoints()).add(endPos).build();
      PathGraph graph = processCfg(cfg, waypoints);
      
      PathGraph resGraph = graph;
      
      /* Append global graph into graph */
      PathGraph globalGraph = getGlobalGraph(Identifiers.GLOBAL_CFG);
      if(globalGraph != null)
      	resGraph = PathGraph.connect(globalGraph, resGraph);
      
      /* Function inline */
      resGraph = funcProcessor.processFunctionCall(resGraph, waypoints);
      
      IOUtils.stats().pln("Building graph took time: " + timer.stop());
      
      pathEncoder.encode(preprocessor, resGraph);
      
      return pathEncoder.runIsValid();
    } catch (PathFactoryException e) {
      throw new RunProcessorException(e);
    }
  }

	@Override
	public boolean processReachability(IRControlFlowGraph mainCfg, String label)
	    throws RunProcessorException {
		try {
			
			/* Pre-processing the graph */
			
			PreProcessor<?> preprocessor = null;
			if(mode.hasPreprocessor()) {
		    File file = new File(mainCfg.getSourceNode().getLocation().file);
		    CSymbolTable symbolTable = symbolTables.get(file);
		    preprocessor = mode.buildPreprocessor(symbolTable);
			}
			
			timer.start();
			
	    /* Build the graph for this run */
	    PathGraph graph = processCfg(mainCfg, Collections.<Position>emptyList());
	    
	    PathGraph resGraph = graph;
	    
	    /* Append global graph into graph */
			PathGraph globalGraph = getGlobalGraph(Identifiers.GLOBAL_CFG);
			if(globalGraph != null)
				resGraph = PathGraph.connect(globalGraph, resGraph);
			
			/* Function inline */
			resGraph = funcProcessor.processFunctionCall(resGraph);
			
      IOUtils.stats().pln("Building graph took time: " + timer.stop());
			
			pathEncoder.checkReach(preprocessor, resGraph, label);
			return pathEncoder.runIsReachable();
			
		} catch (PathFactoryException e) {
			throw new RunProcessorException(e);
		}
	}

	@Override
	public Table<Integer, Integer, Boolean> processReachabilityIncremental(
			IRControlFlowGraph mainCfg, String label)
	    throws RunProcessorException {
		
		try {
			/* Pre-processing the graph */
			
			PreProcessor<?> preprocessor = null;
			if(mode.hasPreprocessor()) {
		    File file = new File(mainCfg.getSourceNode().getLocation().file);
		    CSymbolTable symbolTable = symbolTables.get(file);
		    preprocessor = mode.buildPreprocessor(symbolTable);
			}
			
	    /* Build the graph for this run */
			timer.start();
			
	    PathGraph graph = processCfg(mainCfg, Collections.<Position>emptyList());
	    
	    PathGraph resGraph = graph;
	    
	    /* Append global graph into graph */
			PathGraph globalGraph = getGlobalGraph(Identifiers.GLOBAL_CFG);
			if(globalGraph != null)
				resGraph = PathGraph.connect(globalGraph, resGraph);
			
      IOUtils.stats().pln("Build non-func-inline graph took: " + timer.stop());
			
      Table<Integer, Integer, Boolean> resTable = HashBasedTable.create();
			int iterBound = Preferences.getInt(Preferences.OPTION_ITERATION_TIMES);
			
			/* Function inline */
			int funcInlineLevel = Preferences.isSet(Preferences.OPTION_FUNC_INLINE) ?
					Preferences.getInt(Preferences.OPTION_FUNC_INLINE) : 0;
			
			PathGraph preInline = resGraph;
			for(int currLevel = 0; currLevel <= funcInlineLevel; currLevel++) {
				PathGraph postInline;
				
				if(currLevel == 0) {
					postInline = preInline;
				} else {
					timer.start();
					postInline = funcProcessor.processFuncCallWithEffortLevelOne(preInline);			      
					if(preInline.equals(postInline)) break; // nothing to be in-lined
					IOUtils.stats().pln("Build func-inline graph took: " + timer.stop());
				}
				
				pathEncoder.checkReachIncremental(preprocessor, postInline, label);
				boolean isReachable = pathEncoder.runIsReachable();
				resTable.put(currLevel, iterBound, isReachable);
				
				StringBuilder sb = new StringBuilder().append('{')
						.append(iterBound)
						.append(':')
						.append(funcInlineLevel)
						.append("} ")
						.append(isReachable ? "UNSAFE" : "SAFE");
				IOUtils.err().println(sb.toString());
				
				preInline = postInline;
			}
			
			return resTable;
			
		} catch (PathFactoryException e) {
			throw new RunProcessorException(e);
		}
	}
	
	@Override
	public PathGraph processCfg(IRControlFlowGraph cfg, Collection<Position> waypoints) 
			throws RunProcessorException {
		Preconditions.checkNotNull(cfg);
		Preconditions.checkNotNull(waypoints);
		
	  File file = new File(cfg.getSourceNode().getLocation().file);
	  CSymbolTable symbolTable = symbolTables.get(file);
	  Scope oldScope = symbolTable.getCurrentScope();
	  symbolTable.enterScope(cfg);
	  
	  IRBasicBlock startBlock = cfg.getEntry();
	  IRBasicBlock endBlock = cfg.getExit();
	  
	  /* Get graph */
	  PathGraph graph = processRunBtwnBlocks(startBlock, endBlock, waypoints, cfg, symbolTable);
	  
	  /* Graph in-line */
	  PathGraph resGraph = loopProcessr.loopInline(cfg, graph, waypoints);
	  
	  symbolTable.setScope(oldScope);
	  
	  resGraph = PathGraph.simplify(cfg, resGraph);
	  
	  assert(resGraph.isValid());
	  
	  return resGraph;
	}

	/**
	 * Process run between blocks: <code>startBlock</code>, <code>endBlock</code> 
	 * and <code>waypoints</code>
	 * @param startBlock
	 * @param endBlock
	 * @param waypoints
	 * @param cfg
	 * @param symbolTable
	 * @return
	 * @throws RunProcessorException
	 */
	@Override
	public PathGraph processRunBtwnBlocks(
			IRBasicBlock startBlock, 
			IRBasicBlock endBlock, 
			Collection<Position> waypoints, 
			IRControlFlowGraph cfg, 
			CSymbolTable symbolTable) 
					throws RunProcessorException {
		Preconditions.checkNotNull(startBlock);
		Preconditions.checkNotNull(endBlock);
		Preconditions.checkNotNull(cfg);
		Preconditions.checkNotNull(waypoints);
		
	  if(waypoints.isEmpty()) 
	  	return buildGraphBtwnBlocks(cfg, startBlock, endBlock);
	  
	  PathGraph graph = null;
	  IRBasicBlock currBlock = startBlock;
	
	  for(Position pos : waypoints) {
	  	IOUtils.debug().pln(pos.toString()).flush();
	      
	  	if (currBlock == null)
	  		throw new RunProcessorException("Function ended before end of run.");
	  	
	  	/* Split cfg at current position 'pos' to add statements */
	  	Pair<? extends IRBasicBlock, ? extends IRBasicBlock> pair = 
	  			cfg.splitAt(pos, pos.hasLoop(), 
	  					InsertionType.BEFORE.equals(pos.getInsertionType()));
	  	
	  	IRBasicBlock target = pair.fst();
	  	IRBasicBlock nextCurrBlock = pair.snd();
	  	
	  	PathGraph wayGraph = null;
	  	
	  	if(target != null) {
	    	if(currBlock != target) {
	    		wayGraph = buildGraphBtwnBlocks(cfg, currBlock, target);
	    	} else {
	    		/* FIXME: if source block and target block are same, 
	    		 * if there's loop in cfg between them, call buildPathGraphToBlock
	    		 * would get the graph between them, otherwise, would build an
	    		 * empty graph. We want to avoid it by just creating a single 
	    		 * graph with a single block.
	    		 */
	    		wayGraph = PathGraph.createSingleton(Path.createForBlock(currBlock));
	    	}
	  	}
	  	
	  	/* Collect statements attached with pos in control file */
	  	List<IRStatement> stmts = processPosition(pos, symbolTable);
	  	if(!stmts.isEmpty()) {
	  		Path annoPath = Path.create(stmts);
	  		if(wayGraph != null) {
	  			wayGraph = PathGraph.addPostPath(wayGraph, annoPath);
	  		} else {
	  			wayGraph = PathGraph.createSingleton(annoPath);
	  		}
	  	}
	  	
	  	/* Attach wayGraph to graph */
	  	if(graph == null)     graph = wayGraph;
	  	else                  graph = PathGraph.connect(graph, wayGraph);
	    	
	  	/* Process the block after pos */
	  	currBlock = nextCurrBlock;
	  }
	  
	  { /* End position */
	    PathGraph endGraph = buildGraphBtwnBlocks(cfg, currBlock, endBlock);
	    
	    if(graph == null)     graph = endGraph;
	    else                  graph = PathGraph.connect(graph, endGraph);
	  }
	  
	  assert(graph.isValid());
	  return graph;
	}

	/** Incorporate the command for the given position into the given path. */
  private List<IRStatement> processPosition(Position position, CSymbolTable symbolTable) 
  		throws RunProcessorException {
    List<IRStatement> stmts = Lists.newArrayList();
    
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
          cAnalyzer.analyze(spec, symbolTable.getOriginalSymbolTable());
          
          /*
           * TODO: modifications to the symbol table by the analyzer are ignored.
           */
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
          stmts.add(Statement.assertStmt(fun, argExprs.get(0)));
        } else if (funName.trim().equals("cascade_assume")) {
          stmts.add(Statement.assumeStmt(fun, argExprs.get(0)));
        } else {
          throw new RunProcessorException("Unknown Cascade function: " + funName);
        }
        
      } catch (IOException e) {
        throw new RunProcessorException("Specification parse failure", e);
      } catch (ParseException e) {
        throw new RunProcessorException("Specification parse failure", e);
      }
    }

    return stmts;
  }
  
  /**
	 * Build a graph between <code>start</code> and <code>target
	 * </code>, and insert loop graphs if there are loop blocks
	 * in the block set inside the graph.
	 * 
	 * @param cfg
	 * @param start
	 * @param target
	 * @return
	 * @throws RunProcessorException
	 */
  private PathGraph buildGraphBtwnBlocks(IRControlFlowGraph cfg,
      final IRBasicBlock start, IRBasicBlock target)
      		throws RunProcessorException {
  	Preconditions.checkNotNull(start);
  	Preconditions.checkNotNull(target);
  	
  	if(start.equals(target) && !Type.LOOP.equals(start.getType()))
  		return PathGraph.createSingleton(Path.createForBlock(start));
  	
    /* Find all edges from start to target, using a backwards BFS.*/  
    IRControlFlowGraph newCFG = cfg.findPathsBtwnBlocks(start, target);
    		
    if(newCFG.isEmpty())
    	throw new RunProcessorException("Failure to build graph from " + start 
    			+ " to " + target);
    
    /* Build path-CFG from edges */
    Multimap<Path, Path> predecessorMap = HashMultimap.create();
    
    for(IRBasicBlock block : newCFG.getBlocks()) {
      Path targetPath = Path.createForBlock(block);
      for(IREdge<?> edge : newCFG.getIncomingEdges(block)) {
      	IRBasicBlock src = edge.getSource();
      	Path srcPath = Path.createForBlock(src);
      	if(edge.getGuard() == null) {
      		predecessorMap.put(targetPath, srcPath);
      	} else {
      		/* edge has guard, attach "PathEdge" label to path */
      		IRStatement stmt = Statement.assumeStmt(edge.getSourceNode(), edge.getGuard());
      		Path edgePath  = Path.create(stmt);
      		edgePath.labelEdgePath();
      		predecessorMap.put(edgePath, srcPath);
      		predecessorMap.put(targetPath, edgePath);
      	}
      }
    }
    
    PathGraph resGraph = PathGraph.create(predecessorMap, 
    		Path.createForBlock(start), Path.createForBlock(target));
    
    /* Collect loop blocks */
    Iterable<? extends IRBasicBlock> loopBlocks = Iterables.filter(newCFG.getBlocks(), 
    		new Predicate<IRBasicBlock>() {
			@Override
			public boolean apply(IRBasicBlock block) {
				return !block.equals(start) && 
						IRBasicBlock.Type.LOOP.equals(block.getType()) && 
	          block.getIterTimes() > 0;
			}
    });
    
    /* build loop in-line map */
    
    Map<Path, PathGraph> loopInlineCandMap = Maps.newHashMap();
    for(IRBasicBlock loopBlock : loopBlocks) {
    	Path srcPath = Path.createForBlock(loopBlock);
    	PathGraph singleLoop = buildGraphBtwnBlocks(cfg, loopBlock, loopBlock);
    	PathGraph.labelLoop(singleLoop, loopBlock.getIterTimes());
    	loopInlineCandMap.put(srcPath, singleLoop.clone());
    }
    
    /* loop in-line */
    
    return PathGraph.insertInlineMap(resGraph, loopInlineCandMap);
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

	private PathGraph getGlobalGraph(final String id) throws RunProcessorException {	
		IRControlFlowGraph globalCFG = Iterables.find(cfgs.values(), 
				new Predicate<IRControlFlowGraph>() {
			@Override
			public boolean apply(IRControlFlowGraph cfg) {
				return id.equals(cfg.getName());
			}
		});
		
		return processCfg(globalCFG, Collections.<Position>emptyList());
	}
}