package edu.nyu.cascade.c;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.util.Collection;
import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;

import xtc.parser.ParseException;
import xtc.parser.Result;
import xtc.tree.Node;
import xtc.util.SymbolTable.Scope;
import edu.nyu.cascade.control.LoopPoint;
import edu.nyu.cascade.control.Position;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.impl.Statement;
import edu.nyu.cascade.util.IOUtils;

public class LoopInlineProcessor {
  private final RunProcessor<PathGraph> processor;
  private final Map<File, CSymbolTable> symbolTables;
  private final CAnalyzer cAnalyzer;
	
	private LoopInlineProcessor(RunProcessor<PathGraph> processor,
      Map<File, CSymbolTable> symbolTables,
      CAnalyzer cAnalyzer) {
    this.processor = processor;
    this.symbolTables = symbolTables;
    this.cAnalyzer = cAnalyzer;
	}
	
  public static LoopInlineProcessor create(
  		RunProcessor<PathGraph> processor,
      Map<File, CSymbolTable> symbolTables, CAnalyzer cAnalyzer) {
  	return new LoopInlineProcessor(processor, symbolTables, cAnalyzer);
  }
  
  /**
	 * In-line the loop graph with loop point specified via <code>waypoints
	 * </code> in the control file into the original <code>graph</code>.
	 * 
	 * @param cfg
	 * @param graph
	 * @param waypoints
	 * @return
	 * @throws RunProcessorException
	 */
	PathGraph loopInline(IRControlFlowGraph cfg,
			PathGraph graph,
			Collection<Position> waypoints) 
					throws RunProcessorException {
		Preconditions.checkNotNull(waypoints);
		
		Iterable<Position> loopPoints = Iterables.filter(waypoints, 
				new Predicate<Position>(){
			@Override
			public boolean apply(Position position) {
				return position.hasLoop();
			}
		});
	 	
	  Map<Path, PathGraph> loopInlineMap = getLoopInlineMap(
	  		cfg, graph, loopPoints);
	  
	  if(loopInlineMap.isEmpty()) return graph;
	
	  return PathGraph.insertInlineMap(graph, loopInlineMap);
	}

	/**
   * Process the position <code>pos</code> that has loop point declared
   * in it. If any invariant is specified at <code>pos</code>, return
   * the graph with invariant, otherwise, just return the loop graph.
   * 
   * @throws RunProcessorException
   */
  private PathGraph processLoopPoint(IRControlFlowGraph cfg, Position pos) 
  		throws RunProcessorException {
  	Preconditions.checkNotNull(pos);
  	Preconditions.checkArgument(pos.hasLoop());
  	
  	Iterable<LoopPoint> loopPosInv = Iterables.filter(pos.getLoops(), new Predicate<LoopPoint>(){
			@Override
      public boolean apply(LoopPoint loopPos) {
	      return loopPos.hasInvariant();
      }
  	});
  	
  	/* Only has single loop positions with invariant */
  	assert(Iterables.size(loopPosInv) <= 1);
  	
  	/* Clear default iteration times if user specifies in control file */
  	IRBasicBlock entryBlock = cfg.bestBlockForPosition(pos, pos.hasLoop());
  	entryBlock.clearIterTimes();
  	
  	CSymbolTable symbolTable = symbolTables.get(pos.getFile());
  	Scope currScope = symbolTable.getCurrentScope();
  	symbolTable.setScope(entryBlock.getScope());
  	
  	PathGraph resGraph = null;
  	
  	/* Get the loop graph, and tag the back paths and out paths */
  	for(LoopPoint loopPos : pos.getLoops()) {
  		
  		PathGraph loopGraph = processor.processRunBtwnBlocks(entryBlock, entryBlock, 
  				loopPos.getWayPoint(), cfg, symbolTable);
  		
			/* clone to keep paths isolated from out-loop, not mess up the iteration times */
  		PathGraph loopClone = loopGraph.clone();
  		PathGraph.labelLoop(loopClone, loopPos.getIterTimes());
  		
  		/* In-line nested loops */
  		PathGraph inlinedLoop = loopInline(cfg, loopClone, loopPos.getWayPoint());

  		PathGraph tmpGraph = inlinedLoop;
  		if(loopPos.hasInvariant()) {
  			/* Ignore loop iteration when it has loop invariant */
  			tmpGraph.getSrcPath().labelLoopEntry(0); // clean iteration-times to avoid unroll
  			tmpGraph = processInvariant(tmpGraph, loopPos, symbolTable);
  		}
  		
    	if(resGraph == null) resGraph = tmpGraph;
    	else								 resGraph = PathGraph.connect(resGraph, tmpGraph);
  	}
	  
  	resGraph = PathGraph.simplify(cfg, resGraph);
	  
	  assert(resGraph.isValid());
  
  	symbolTable.setScope(currScope);
  	return resGraph;
  }
  
  /**
   * Get the map from loop entry path to the loop graph to be in-lined,
   * according to <code>loopPoints</code> in the control file.
   * 
   * @param cfg
   * @param graph
   * @param loopPoints
   * @return
   * @throws RunProcessorException
   */
  private Map<Path, PathGraph> getLoopInlineMap(
  		IRControlFlowGraph cfg,
  		PathGraph graph,
  		Iterable<Position> loopPoints) throws RunProcessorException {
		Preconditions.checkNotNull(loopPoints);
	  Map<Path, PathGraph> replaceMap = Maps.newHashMap();
	  
	  for(Position pos : loopPoints) {
	  	Path loopPath = graph.getPathForLoopPos(pos);
	  	PathGraph loopGraph = processLoopPoint(cfg, pos);
	  	assert(loopGraph.isValid());
	  	replaceMap.put(loopPath, loopGraph);
	  }
	  
	  return replaceMap;
  }
  
  /**
   * Parse the invariant of loop specified at <code>loopPoint</code>
   * in the control file, and attach it to the entry path of the 
   * <code>loopGraph</code>
   * 
   * @param loopGraph
   * @param loopPos
   * @param symbolTable
   * @return
   * @throws RunProcessorException
   */
  private PathGraph processInvariant(PathGraph loopGraph, LoopPoint loopPos, 
      CSymbolTable symbolTable) throws RunProcessorException {
    Preconditions.checkArgument(loopGraph.isLoop());
  	
    try {
    	
      CSpecParser specParser = new CSpecParser(new StringReader(loopPos.getInvariant()),
      		loopPos.getFile().getPath());
      Result specResults = specParser.pCSpecExpression(0);
      Node spec = (Node) specParser.value(specResults);
//      Location loc = new Location(loopPos.getFile().getPath(), loopPos.getLine().intValue(), 0);
//      spec.setLocation(loc);
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
      
    	IRStatement assumeStmt = Statement.assumeStmt(spec, argExpr);
    	IRStatement assertStmt = Statement.assertStmt(spec, argExpr);
    	
    	return PathGraph.getHavocLoop(loopGraph, assumeStmt, assertStmt);
      
    } catch (IOException e) {
      throw new RunProcessorException("Specification parse failure", e);
    } catch (ParseException e) {
      throw new RunProcessorException("Specification parse failure", e);
    }
  }
}
