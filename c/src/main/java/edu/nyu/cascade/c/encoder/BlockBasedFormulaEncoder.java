package edu.nyu.cascade.c.encoder;

import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.SafeResult;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRTraceNode;
import edu.nyu.cascade.ir.IRStatement.StatementType;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.impl.LoopInfo;
import edu.nyu.cascade.ir.impl.Statement;
import edu.nyu.cascade.ir.impl.TraceFactory;
import edu.nyu.cascade.ir.path.PathEncoding;
import edu.nyu.cascade.ir.path.PathFactoryException;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateExpressionClosure;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;

/**
 * Encodes a program path as a verification condition and checks the condition
 * for validity. Also optionally checks the path for feasibility (e.g., the path
 * (x := 0; assume x > 0; assert false) is invalid but infeasible).
 */

public class BlockBasedFormulaEncoder implements FormulaEncoder {
	private static final String AttachAsserts = "attach_asserts";
  
	private final PathStateFactory pathStateFactory;
	private final StmtBasedFormulaEncoder stmtFormulaEncoder;
	private final Map<IRBasicBlock, StateClosure> cleanBlockStateClosureMap;
	private final Map<IREdge<?>, StateClosure> cleanEdgeStateClosureMap;
	private final PathEncoding pathEncoding;
	private SafeResult runIsValid, runIsReachable;
	private boolean checkFeasibility;
	private boolean checkExitUnroll, checkKeepUnroll;
	
  private BlockBasedFormulaEncoder(PathEncoding pathEncoding, TraceFactory traceFactory) {
  	this.pathEncoding = pathEncoding;
    pathStateFactory = PathStateFactory.getInstance(pathEncoding);
    stmtFormulaEncoder = StmtBasedFormulaEncoder.create(pathEncoding, traceFactory);
  	cleanBlockStateClosureMap = Maps.newHashMap();
  	cleanEdgeStateClosureMap = Maps.newHashMap();
    reset();
  }

  public static BlockBasedFormulaEncoder create(PathEncoding encoding, TraceFactory traceFactory) {
    return new BlockBasedFormulaEncoder(encoding, traceFactory);
  }
  
  @Override
  public void enableCheckExitUnroll() {
  	stmtFormulaEncoder.enableCheckExitUnroll();
  	checkExitUnroll = true;
  }
  
  @Override
  public void enableCheckKeepUnroll() {
  	stmtFormulaEncoder.enableCheckKeepUnroll();
  	checkKeepUnroll = true;
  }
  
  @Override
  public boolean checkKeepUnroll() throws PathFactoryException {
  	return stmtFormulaEncoder.checkKeepUnroll();
  }
  
  @Override
  public boolean checkExitUnroll() throws PathFactoryException {
  	return stmtFormulaEncoder.checkExitUnroll();
  }
  
  @Override
  public void setIterTimes(int iterTimes) {
  	stmtFormulaEncoder.setIterTimes(iterTimes);
  }
  
  @Override
  public void reset() {
  	checkExitUnroll = false;
  	checkKeepUnroll = false;
    checkFeasibility = false;
    runIsValid = SafeResult.valid();
    runIsReachable = SafeResult.valid();
    cleanBlockStateClosureMap.clear();
    cleanEdgeStateClosureMap.clear();
  }
  
  @Override
  public SafeResult runIsReachable() {
  	return runIsReachable;
  }
  
  @Override
  public SafeResult runIsValid() {
    return runIsValid;
  }

	@Override
  public void setFeasibilityChecking(boolean b) {
  	checkFeasibility = b;
  }

	@Override
  public void encode(final PreProcessor<?> preprocessor, final IRControlFlowGraph cfg,
  		LoopInfo loopInfo) throws PathFactoryException {
		
  	boolean mergeLoopUnroll = Preferences.isSet(Preferences.OPTION_MERGE_UNROLL);
  	
  	/* Pre-processing for mode Partition and Burstall */
  	stmtFormulaEncoder.preprocess(preprocessor, cfg, loopInfo, mergeLoopUnroll);
  	
  	final TraceFactory factory = new TraceFactory();
  	
		BlockEncodingStrategy<StateExpression> blockStrategy = new BlockEncodingStrategy<StateExpression>() {
			@Override
			public Pair<Boolean, StateExpression> apply(IRBasicBlock block, StateExpression preState) 
					throws PathFactoryException {
				return encodeBlock(factory, block, preState);
			}
		};
		
		EdgeEncodingStrategy<StateExpression> edgeStrategy = new EdgeEncodingStrategy<StateExpression>() {
			@Override
			public Pair<Boolean, StateExpression> apply(IREdge<?> edge, StateExpression preState) 
					throws PathFactoryException {
				return encodeEdge(factory, edge, preState);
			}
		};
		
		PhiNodeResolveStrategy<StateExpression> mergeStrategy = new PhiNodeResolveStrategy<StateExpression>() {
			@Override
      public StateExpression apply(Collection<StateExpression> preStates) {
				Preconditions.checkArgument(!preStates.isEmpty());
	      return pathEncoding.noop(preStates);
      }
		};
		
		TraceEncodeStrategy traceEncodeStrategy = new TraceEncodeStrategy() {
			@Override
			public void encode(IREdge<?> edge) {
				IRBasicBlock srcBlock = edge.getSource();
				IRBasicBlock destBlock = edge.getTarget();
				IRTraceNode srcNode = factory.getTraceNode(srcBlock);
				IRTraceNode destNode = factory.getTraceNode(destBlock);
				IRTraceNode edgeNode = factory.create(edge);
				srcNode.addSuccessor(edgeNode);
				edgeNode.addSuccessor(destNode);
			}

			@Override
			public void encode(IRBasicBlock block) {
				factory.create(block);
			}
		};
		
		MemLeakCheckStrategy<StateExpression> memLeakCheckStrategy = new MemLeakCheckStrategy<StateExpression>() {
			@Override
      public void apply(StateExpression state) throws PathFactoryException {
				if(!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) return;
				
				StateFactory<?> stateFactory = pathEncoding.getStateFactory();
				Expression memory_no_leak = stateFactory.applyMemoryTrack(state);
				stmtFormulaEncoder.checkAssertion(state, memory_no_leak, Identifiers.VALID_MEMORY_TRACE);
      }
		};
  	
		stmtFormulaEncoder.statePropagateDFS(cfg, 
				loopInfo, 
				blockStrategy, 
				edgeStrategy, 
				mergeStrategy, 
				traceEncodeStrategy,
				memLeakCheckStrategy,
				mergeLoopUnroll,
				checkExitUnroll,
				checkKeepUnroll,
				pathEncoding.emptyState());
		CScopeAnalyzer.reset();
  }
  
  @Override
  public void checkReach(final PreProcessor<?> preprocessor, 
  		IRControlFlowGraph cfg, LoopInfo loopInfo, final String label) 
  				throws PathFactoryException {
  	boolean mergeLoopUnroll = Preferences.isSet(Preferences.OPTION_MERGE_UNROLL);
  	
  	/* Pre-processing for mode Partition and Burstall */
  	stmtFormulaEncoder.preprocess(preprocessor, cfg, loopInfo, mergeLoopUnroll);
  	
  	final TraceFactory factory = new TraceFactory();
  	
		BlockEncodingStrategy<StateExpression> blockStrategy = new BlockEncodingStrategy<StateExpression>() {
			@Override
			public Pair<Boolean, StateExpression> apply(IRBasicBlock block, StateExpression preState) 
					throws PathFactoryException {
				return checkReachBlock(factory, block, preState, label);
			}
		};
		
		EdgeEncodingStrategy<StateExpression> edgeStrategy = new EdgeEncodingStrategy<StateExpression>() {
			@Override
			public Pair<Boolean, StateExpression> apply(IREdge<?> edge, StateExpression preState) 
					throws PathFactoryException {
				return encodeEdge(factory, edge, preState);
			}
		};
		
		PhiNodeResolveStrategy<StateExpression> mergeStrategy = new PhiNodeResolveStrategy<StateExpression>() {
			@Override
      public StateExpression apply(Collection<StateExpression> preStates) {
				Preconditions.checkArgument(!preStates.isEmpty());
	      return pathEncoding.noop(preStates);
      }
		};
		
		TraceEncodeStrategy traceEncodeStrategy = new TraceEncodeStrategy() {			
			@Override
			public void encode(IREdge<?> edge) {
				IRBasicBlock srcBlock = edge.getSource();
				IRBasicBlock destBlock = edge.getTarget();
				IRTraceNode srcNode = factory.getTraceNode(srcBlock);
				IRTraceNode destNode = factory.getTraceNode(destBlock);
				IRTraceNode edgeNode = factory.create(edge);
				srcNode.addSuccessor(edgeNode);
				edgeNode.addSuccessor(destNode);
			}

			@Override
			public void encode(IRBasicBlock block) {
				factory.create(block);
			}
		};
		
		MemLeakCheckStrategy<StateExpression> memLeakCheckStrategy = new MemLeakCheckStrategy<StateExpression>() {
			@Override
      public void apply(StateExpression state) throws PathFactoryException {
				return;
      }
		};
		
		stmtFormulaEncoder.statePropagateDFS(cfg, 
				loopInfo, 
				blockStrategy, 
				edgeStrategy, 
				mergeStrategy, 
				traceEncodeStrategy,
				memLeakCheckStrategy,
				mergeLoopUnroll,
				checkExitUnroll,
				checkKeepUnroll,
				pathEncoding.emptyState());
		
		CScopeAnalyzer.reset();
  }
	
	@Override
	public Pair<Boolean, StateExpression> checkReachBlock(
			TraceFactory factory,
			IRBasicBlock block,
	    StateExpression preState, 
	    String label) throws PathFactoryException {
  	if(block.getPreLabels().contains(label)) {
			IOUtils.out().println("Checking path reachability.");
      SatResult<?> res = pathEncoding.checkPath(preState);
      runIsReachable = SafeResult.valueOf(res);
      if(!runIsReachable.isSafe()) return Pair.of(false, preState);
		}
  	
  	// FIXME: how to add statement to trace node
  	StateClosure stateClosure = getBlockStateClosure(block);
  	StateExpression postState = stateClosure.apply(preState);
  	return Pair.of(true, postState);
	}

	/** Encode <code>edge</code> with a <code>preState</code> 
	 * @throws PathFactoryException */
	@Override
  public Pair<Boolean, StateExpression> encodeEdge(
  		TraceFactory factory,
  		IREdge<?> edge, 
  		StateExpression preState) 
  				throws PathFactoryException {
  	if(edge.getGuard() == null) return Pair.of(true, preState);
  	// FIXME: how to add statement to trace node
  	StateExpression postState = getEdgeStateClosure(edge).apply(preState);
  	return Pair.of(true, postState);
  }
  
	@Override
  public Pair<Boolean, StateExpression> encodeBlock(
  		TraceFactory factory, 
  		IRBasicBlock block, 
  		StateExpression preState) 
  				throws PathFactoryException {
  	StateClosure stateClosure = getBlockStateClosure(block);
  	StateExpression postState = stateClosure.apply(preState);
  	
  	// FIXME: how to add statement to trace node
  	@SuppressWarnings("unchecked")
    Map<StateClosure, StateExpressionClosure> attachAssertions = 
  			(Map<StateClosure, StateExpressionClosure>) stateClosure.getProperty(AttachAsserts);
  	
  	boolean succeed = false;
    for(Entry<StateClosure, StateExpressionClosure> attachAssertion : attachAssertions.entrySet()) {
    	StateClosure assertStateClosure = attachAssertion.getKey();
    	StateExpression assertState = assertStateClosure.apply(preState);
    	StateExpressionClosure assertStateExprClosure = attachAssertion.getValue();
      succeed = checkAssertion(assertState, assertStateExprClosure.eval(assertState)); // check assertion
      if(!succeed) return Pair.of(succeed, postState); // return false to interrupt encoding
    }
    return Pair.of(succeed, postState);
  }

	@Override
	public IRTraceNode getErrorTrace(IRControlFlowGraph cfg) {
		return stmtFormulaEncoder.getErrorTrace(cfg);
	}

	/**
	 * Get the state closure for <code>block</code>, if <code>
	 * cleanBlockStateClosureMap</code> has it, just return the 
	 * related state closure
	 * 
	 * @param block
	 * @return the clean state closure of block
	 * @throws PathFactoryException 
	 */
	private StateClosure getBlockStateClosure(IRBasicBlock block) throws PathFactoryException {
		if(cleanBlockStateClosureMap.containsKey(block)) 
			return cleanBlockStateClosureMap.get(block);
		
  	Map<StateClosure, StateExpressionClosure> attachAssertions = Maps.newHashMap();
  	
		StateExpression postState = pathEncoding.emptyState();
	  for(IRStatement stmt : block.getStatements()) { 
	  	IOUtils.debug().pln("Encoding: " + stmt);
	  	postState = stmtFormulaEncoder.encodeStatement(stmt, postState);
	  	if(StatementType.ASSERT.equals(stmt.getType())) {
	  		// Keep the copy of the postState of assertion, which will be changed
	  		// in the following state encoding
	  		
	  		StateFactory<?> stateFactory = pathEncoding.getStateFactory();
	  		
	  		StateExpression postStateCopy = stateFactory.copy(postState);
	  		StateClosure assertStateClosure = pathStateFactory.getStateClosure(postStateCopy);
	  		ExpressionEncoder exprEncoder = pathEncoding.getExpressionEncoder();
	  		
  			StateExpression emptyState = stateFactory.freshState();
  			Expression assertExpr = stmt.getPreCondition(emptyState, exprEncoder);
  			attachAssertions.put(assertStateClosure, stateFactory.suspend(emptyState, 
  					assertExpr));
    	}
	  }
	  
		StateClosure stateClosure = pathStateFactory.getStateClosure(postState);
	  if(!attachAssertions.isEmpty()) {
	  	stateClosure.setProperty(AttachAsserts, attachAssertions);
	  }
	  
		cleanBlockStateClosureMap.put(block, stateClosure);
		return stateClosure;
	}

	/**
	 * Get the clean state closure for <code>edge</code>, if <code>
	 * cleanEdgeStateClosureMap</code> stored it, just return the 
	 * related state closure
	 * 
	 * @param edge
	 * @return the clean state closure of edge
	 * @throws PathFactoryException 
	 */
	private StateClosure getEdgeStateClosure(IREdge<?> edge) throws PathFactoryException {
		if(cleanEdgeStateClosureMap.containsKey(edge)) 
			return cleanEdgeStateClosureMap.get(edge);
		
		IRStatement assumeStmt = Statement.assumeStmt(edge.getSourceNode(), edge.getGuard());
		IOUtils.debug().pln("Encoding: " + assumeStmt);
		StateExpression emptyState = pathEncoding.emptyState();
		StateExpression postState = stmtFormulaEncoder.encodeStatement(assumeStmt, emptyState);  	
		StateClosure stateClosure = pathStateFactory.getStateClosure(postState);
		cleanEdgeStateClosureMap.put(edge, stateClosure);
		return stateClosure;
	}

	/**
	 * Check the <code>assertion</code> with current state <code>preCond</code>
	 * 
	 * @param preCond
	 *          the current state
	 * @param assertion
	 * 
	 * @return false if the assertion results in an invalid verification condition
	 *         or an infeasible path; true otherwise.
	 */
	private boolean checkAssertion(StateExpression preCond, Expression assertion) 
	    throws PathFactoryException {
		/* If the statement has a precondition, we have to check it before continuing with 
		 * the encoding.
		 */
		IOUtils.debug().pln("Checking assertion: " + assertion).flush();
		ValidityResult<?> result = pathEncoding.checkAssertion(preCond, assertion);
		runIsValid = SafeResult.valueOf(result);
		
		if (!runIsValid.isSafe()) return false;
		
		if (checkFeasibility) {
			IOUtils.out().println("Checking path feasibility.");
			SatResult<?> res = pathEncoding.checkPath(preCond);
			if (!res.isSatisfiable()) {
				IOUtils.err().println("WARNING: path assumptions are unsatisfiable");
				return false;
			}
	  }
	  return true;
	}
}
