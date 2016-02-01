package edu.nyu.cascade.c;

import java.io.File;
import java.util.Map;

import javax.xml.bind.JAXBElement;

import xtc.tree.Node;

import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;

import edu.nyu.cascade.c.CAnalyzer;
import edu.nyu.cascade.c.encoder.BlockBasedFormulaEncoder;
import edu.nyu.cascade.c.encoder.FormulaEncoder;
import edu.nyu.cascade.c.encoder.StmtBasedFormulaEncoder;
import edu.nyu.cascade.c.graphml.TraceGraphMLBuilder;
import edu.nyu.cascade.c.mode.Mode;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IRTraceNode;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.impl.LoopInfo;
import edu.nyu.cascade.ir.impl.TraceFactory;
import edu.nyu.cascade.ir.path.PathFactoryException;
import edu.nyu.cascade.ir.path.SimplePathEncoding;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Preferences;
/**
 * A processor for control file runs. It is statement-based.
 * For loop point and function call point, we handle them separately.
 * Create a loop graph for every loop point, and create a function
 * in-line graph for every path contains call statement. In-line them
 * into the original graph.
 */
class RunProcessorImpl implements RunProcessor {

	private RunProcessorImpl(
  		Mode mode,
  		Map<File, CSymbolTable> symbolTables,
      Map<Node, IRControlFlowGraph> cfgs,
      CAnalyzer cAnalyzer) {
    this.symbolTables = symbolTables;
    this.cfgs = cfgs;
    this.mode = mode;
    this.traceFactory = new TraceFactory();
    
    ExpressionEncoder encoder;
    if(Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) 
    	encoder = CExpressionMemCheckEncoder.create(mode);
    else
    	encoder = CExpressionEncoder.create(mode);
    
    formulaEncoder = Preferences.isSet(Preferences.OPTION_PATH_BASED) ?
    		BlockBasedFormulaEncoder.create(SimplePathEncoding.create(encoder), traceFactory) :
    			StmtBasedFormulaEncoder.create(SimplePathEncoding.create(encoder), traceFactory);
    funcProcessor = FuncInlineProcessor.create(this, cfgs, symbolTables);
  }
  
	static RunProcessorImpl create(
  		Mode mode,
  		Map<File, CSymbolTable> symbolTables,
      Map<Node, IRControlFlowGraph> cfgs,
      CAnalyzer cAnalyzer) {
  	return new RunProcessorImpl(mode, symbolTables, cfgs, cAnalyzer);
  }
  
  private final Map<File, CSymbolTable> symbolTables;
  private final Map<Node, IRControlFlowGraph> cfgs;
  private final FormulaEncoder formulaEncoder;
  private final FuncInlineProcessor funcProcessor;
  private final Mode mode;
  private final TraceFactory traceFactory;
  
  @Override
	public void enableFeasibilityChecking() {
	  formulaEncoder.setFeasibilityChecking(true);
	}
  
  @Override
  public boolean prepare(IRControlFlowGraph mainCfg) {
    /* Append global graph into graph */
		IRControlFlowGraph globalCFG = getGlobalCFG(Identifiers.GLOBAL_CFG);
		
		if(globalCFG != null)
			CfgProcessor.appendPreCFG(globalCFG, mainCfg);
				
		/* Function in-line */
		funcProcessor.functionInlineCFG(mainCfg);
		
		/* Path-based normalization*/
		pathBasedNormalization(mainCfg);
		
		return funcProcessor.hasFunctionCall(mainCfg);
  }
  
	@Override
	public SafeResult processAssertion(IRControlFlowGraph mainCFG, 
			LoopInfo loopInfo, int iterTime) throws RunProcessorException {
		
		try {
			
			/* Set the iteration time */
			formulaEncoder.setIterTimes(iterTime);
			
			/* Build the preprocessor */
			PreProcessor<?> preprocessor = null;
			if(mode.hasPreprocessor()) {
		    File file = new File(mainCFG.getSourceNode().getLocation().file);
		    CSymbolTable symbolTable = symbolTables.get(file);
		    preprocessor = mode.buildPreprocessor(symbolTable);
			}
			
			formulaEncoder.encode(preprocessor, mainCFG, loopInfo);
			return formulaEncoder.runIsValid();
			
		} catch (PathFactoryException e) {
			throw new RunProcessorException(e);
		}
	}
  
	@Override
	public SafeResult processReachability(IRControlFlowGraph mainCFG, 
			LoopInfo loopInfo, String label, int iterTime)
					throws RunProcessorException {
		
		try {
			
			/* Set the iteration time */
			formulaEncoder.setIterTimes(iterTime);
			
			/* Build the preprocessor */
			PreProcessor<?> preprocessor = null;
			if(mode.hasPreprocessor()) {
		    File file = new File(mainCFG.getSourceNode().getLocation().file);
		    CSymbolTable symbolTable = symbolTables.get(file);
		    preprocessor = mode.buildPreprocessor(symbolTable);
			}
			
			formulaEncoder.checkReach(preprocessor, mainCFG, loopInfo, label);
			return formulaEncoder.runIsReachable();
			
		} catch (PathFactoryException e) {
			throw new RunProcessorException(e);
		}
	}
	
	@Override
	public void dumpErrorTrace(IRControlFlowGraph cfg) {
		if(!Preferences.isSet(Preferences.OPTION_TRACE)) return;
		
		IRTraceNode traceEntry = formulaEncoder.getErrorTrace(cfg);
		String fileName = cfg.getLocation().file;
		IOUtils.enableTrace(fileName);
		
		traceFactory.dumpTrace(traceEntry, IOUtils.traceFile());
		
		TraceGraphMLBuilder gmlBuilder = new TraceGraphMLBuilder();
		JAXBElement<?> gml = gmlBuilder.analyzeTrace(traceEntry);
		gmlBuilder.dumpXmlTrace(gml, IOUtils.traceXmlFileStream());
	}
	
	@Override
	public void reset() {
		formulaEncoder.reset();
		traceFactory.reset();
	}
	
	private boolean pathBasedNormalization(IRControlFlowGraph mainCFG) {
		return false;
	}
  
  private IRControlFlowGraph getGlobalCFG(final String id) {	
  	return Iterables.find(cfgs.values(), 
				new Predicate<IRControlFlowGraph>() {
			@Override
			public boolean apply(IRControlFlowGraph cfg) {
				return id.equals(cfg.getName());
			}
		}, null);
	}
  
  @Override
  public void enableCheckKeepUnroll() {
  	formulaEncoder.enableCheckKeepUnroll();
  }
  
  @Override
  public void enableCheckExitUnroll() {
  	formulaEncoder.enableCheckExitUnroll();
  }

	@Override
	public boolean checkKeepUnroll() throws RunProcessorException {
		try {
			return formulaEncoder.checkKeepUnroll();
		} catch (PathFactoryException e) {
			throw new RunProcessorException(e);
		}
	}
	
	@Override
	public boolean checkExitUnroll() throws RunProcessorException {
		try {
			return formulaEncoder.checkExitUnroll();
		} catch (PathFactoryException e) {
			throw new RunProcessorException(e);
		}
	}
}