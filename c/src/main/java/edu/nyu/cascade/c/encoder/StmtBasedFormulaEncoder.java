package edu.nyu.cascade.c.encoder;

import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Queues;
import com.google.common.collect.Sets;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.SafeResult;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRStatement.StatementType;
import edu.nyu.cascade.ir.IRTraceNode;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.impl.Loop;
import edu.nyu.cascade.ir.impl.Statement;
import edu.nyu.cascade.ir.impl.TraceFactory;
import edu.nyu.cascade.ir.impl.LoopInfo;
import edu.nyu.cascade.ir.path.PathEncoding;
import edu.nyu.cascade.ir.path.PathFactoryException;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.TheoremProver;
import edu.nyu.cascade.prover.TheoremProverException;
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

public class StmtBasedFormulaEncoder implements FormulaEncoder {
	
  private class LoopCountDownLatch {
		private final int initTime;
		private int currentTime;
		
		LoopCountDownLatch(int initTime) {
			Preconditions.checkArgument(initTime >= 0);
			this.initTime = initTime;
		}
		
		boolean countDown() {
			if(currentTime == 0) return false;
			currentTime--; return true;
		}
		
		boolean stop() {
			return currentTime == 0;
		}
		
		void reset() {
			currentTime = initTime;
		}
		
		boolean notCountDownYet() {
			return currentTime == initTime;
		}
		
		@Override
		public String toString() {
			return "initTime: " + initTime + ", currTime: " + currentTime;
		}
	}
  
  private class LoopUnrollMerger<T> {
  	private final Multimap<IREdge<?>, T> exitMultiSrcState =
  			LinkedHashMultimap.create();
  	
		/** 
		 * Save the exit <code>state</code> for <code>exitEdge</code> of this round 
		 * of loop unrolling
		 * 
		 * @param exitEdge
		 * @param state
		 */
  	void saveExitEdgeState(IREdge<?> exitEdge, T state) {
  		exitMultiSrcState.put(exitEdge, state);
  	}
  	
		/** 
		 * Merged when exit the current loop. Every exit edge will be mapped to a 
		 * merged exit state.
		 * @throws PathFactoryException 
		 */
  	Map<IREdge<?>, T> getExitEdgeStateMap(EdgeEncodingStrategy<T> edgeStrategy,
  			PhiNodeResolveStrategy<T> mergeStrategy) throws PathFactoryException {
  		Collection<IREdge<?>> exitEdges = exitMultiSrcState.keySet();
  		int exitEdgeSize = exitEdges.size();
  		Map<IREdge<?>, T> resMap = Maps.newHashMapWithExpectedSize(exitEdgeSize);
  		
  		for(IREdge<?> exitEdge : exitEdges) {
  			Collection<T> exitSrcStates = exitMultiSrcState.get(exitEdge);
  			T mergeState = mergeStrategy.apply(exitSrcStates);
  			resMap.put(exitEdge, mergeState);
  		}
  		
  		return resMap;
  	}
  }

	private final PathEncoding pathEncoding;
	private final TraceFactory traceFactory;
	
  private SafeResult runIsValid, runIsReachable;
  private boolean checkFeasibility;
  private boolean checkKeepUnroll, checkExitUnroll;
  private int iterTimes = 0;
			
	private final Map<Loop, LoopCountDownLatch> loopCountDownLatchMap = Maps.newHashMap();
	private final Collection<IRStatement> staticStmts = Sets.newHashSet();
	private final Map<Expression, Collection<? extends IREdge<? extends IRBasicBlock>>> exitUnrollMap = Maps.newLinkedHashMap();
	private final Map<Expression, Collection<? extends IREdge<? extends IRBasicBlock>>> keepUnrollMap = Maps.newLinkedHashMap();
			
  private StmtBasedFormulaEncoder(PathEncoding pathEncoding, TraceFactory traceFactory) {
    this.pathEncoding = pathEncoding;
    this.traceFactory = traceFactory;
    reset();
  }

  public static StmtBasedFormulaEncoder create(PathEncoding encoding, TraceFactory traceFactory) {
    return new StmtBasedFormulaEncoder(encoding, traceFactory);
  }
  
  @Override
  public void setIterTimes(int iterTimes) {
  	this.iterTimes = iterTimes;
  }
  
  @Override
  public void reset() {
    checkFeasibility = false;
    checkExitUnroll = false;
    checkKeepUnroll = false;
    runIsValid = SafeResult.valid();
    runIsReachable = SafeResult.valid();
    loopCountDownLatchMap.clear();
    staticStmts.clear();
    pathEncoding.getStateFactory().reset();
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
  public void enableCheckExitUnroll() {
  	checkExitUnroll = true;
  }
  
  @Override
  public void enableCheckKeepUnroll() {
  	checkKeepUnroll = true;
  }
  
  @Override
  public void encode(final PreProcessor<?> preprocessor, final IRControlFlowGraph cfg,
  		LoopInfo loopInfo) throws PathFactoryException {
  	
  	boolean mergeLoopUnroll = Preferences.isSet(Preferences.OPTION_MERGE_UNROLL);
  	
  	/* Pre-processing for mode Partition and Burstall */
  	preprocess(preprocessor, cfg, loopInfo, mergeLoopUnroll);
  	
		BlockEncodingStrategy<StateExpression> blockStrategy = new BlockEncodingStrategy<StateExpression>() {
			@Override
			public Pair<Boolean, StateExpression> apply(IRBasicBlock block, StateExpression preState) 
					throws PathFactoryException {
				return encodeBlock(traceFactory, block, preState);
			}
		};
		
		EdgeEncodingStrategy<StateExpression> edgeStrategy = new EdgeEncodingStrategy<StateExpression>() {
			@Override
			public Pair<Boolean, StateExpression> apply(IREdge<?> edge, StateExpression preState) 
					throws PathFactoryException {
				return encodeEdge(traceFactory, edge, preState);
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
				if(!Preferences.isSet(Preferences.OPTION_TRACE)) return;
				IRBasicBlock srcBlock = edge.getSource();
				IRTraceNode srcNode = traceFactory.getTraceNode(srcBlock);
				IRTraceNode edgeNode = traceFactory.hasEncodeEdge(edge) ? 
						traceFactory.getTraceNode(edge) : 
							traceFactory.create(edge);
				srcNode.addSuccessor(edgeNode);
			}

			@Override
			public void encode(IRBasicBlock block) {
				if(!Preferences.isSet(Preferences.OPTION_TRACE)) return;
				IRTraceNode traceNode = traceFactory.create(block);
				for(IREdge<?> edge : cfg.getIncomingEdges(block)) {
					if(traceFactory.hasEncodeEdge(edge)) {
						IRTraceNode edgeNode = traceFactory.getTraceNode(edge);
						edgeNode.addSuccessor(traceNode);
						traceFactory.eraseEncodeEdge(edge);
					}
				}
			}
		};
		
		MemLeakCheckStrategy<StateExpression> memLeakCheckStrategy = new MemLeakCheckStrategy<StateExpression>() {
			@Override
      public void apply(StateExpression state) throws PathFactoryException {
				if(!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK)) return;
				
				StateFactory<?> stateFactory = pathEncoding.getStateFactory();
				Expression memory_no_leak = stateFactory.applyMemoryTrack(state);
				checkAssertion(state, memory_no_leak, Identifiers.VALID_MEMORY_TRACE);
      }
		};
		
		statePropagateDFS(cfg, 
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
  public IRTraceNode getErrorTrace(IRControlFlowGraph cfg) {
  	Preconditions.checkArgument(Preferences.isSet(Preferences.OPTION_TRACE));
		IRTraceNode entryNode = traceFactory.getTraceNode(cfg.getEntry());
		traceFactory.filterCounterExample(pathEncoding.getExpressionManager(), entryNode);
		return entryNode;
  }
  
  @Override
  public void checkReach(final PreProcessor<?> preprocessor, 
  		final IRControlFlowGraph cfg, LoopInfo loopInfo, final String label) 
  				throws PathFactoryException {
  	boolean mergeLoopUnroll = Preferences.isSet(Preferences.OPTION_MERGE_UNROLL);
  	
  	/* Pre-processing for mode Partition and Burstall */
  	preprocess(preprocessor, cfg, loopInfo, mergeLoopUnroll);
  	
		BlockEncodingStrategy<StateExpression> blockStrategy = new BlockEncodingStrategy<StateExpression>() {
			@Override
			public Pair<Boolean, StateExpression> apply(IRBasicBlock block, StateExpression preState) 
					throws PathFactoryException {
				return checkReachBlock(traceFactory, block, preState, label);
			}
		};
		
		EdgeEncodingStrategy<StateExpression> edgeStrategy = new EdgeEncodingStrategy<StateExpression>() {
			@Override
			public Pair<Boolean, StateExpression> apply(IREdge<?> edge, StateExpression preState) 
					throws PathFactoryException {
				return encodeEdge(traceFactory, edge, preState);
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
				if(!Preferences.isSet(Preferences.OPTION_TRACE)) return;
				IRBasicBlock srcBlock = edge.getSource();
				IRTraceNode srcNode = traceFactory.getTraceNode(srcBlock);
				IRTraceNode edgeNode = traceFactory.hasEncodeEdge(edge) ? 
						traceFactory.getTraceNode(edge) : 
							traceFactory.create(edge);
				srcNode.addSuccessor(edgeNode);
			}

			@Override
			public void encode(IRBasicBlock block) {
				if(!Preferences.isSet(Preferences.OPTION_TRACE)) return;
				IRTraceNode traceNode = traceFactory.create(block);
				for(IREdge<?> edge : cfg.getIncomingEdges(block)) {
					if(traceFactory.hasEncodeEdge(edge)) {
						IRTraceNode edgeNode = traceFactory.getTraceNode(edge);
						edgeNode.addSuccessor(traceNode);
						traceFactory.eraseEncodeEdge(edge);
					}
				}
			}
		};
		
		MemLeakCheckStrategy<StateExpression> memLeakCheckStrategy = new MemLeakCheckStrategy<StateExpression>() {
			@Override
      public void apply(StateExpression state) throws PathFactoryException {
				return;
      }
		};
		
		statePropagateDFS(cfg, 
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
	
  /** Encode <code>edge</code> with a <code>preState</code> 
   * @throws PathFactoryException */
	@Override
  public Pair<Boolean, StateExpression> encodeEdge(
  		TraceFactory factory, 
  		IREdge<?> edge, 
  		StateExpression preState) 
  				throws PathFactoryException {
		StateExpression preStateClone = pathEncoding.getStateFactory().copy(preState);
  	if(edge.getGuard() == null) return Pair.of(true, preStateClone);
  	
  	IRStatement assumeStmt = Statement.assumeStmt(edge.getSourceNode(), edge.getGuard());
  	StateExpression currState = encodeStatement(assumeStmt, preStateClone);
  	attachTraceExprToEdge(factory, edge, assumeStmt, pathEncoding.getTraceExpression());
  	
  	if(!runIsValid.isSafe())	return Pair.of(false, currState);
  	
  	return Pair.of(true, currState);
  }
  
	@Override
  public Pair<Boolean, StateExpression> checkReachBlock(
  		TraceFactory factory,
  		IRBasicBlock block, 
  		StateExpression preState, 
  		String label) 
  				throws PathFactoryException {
		
		processTraceNode(factory, block);
  	
  	if(block.getPreLabels().contains(label)) {
      SatResult<?> res = pathEncoding.checkPath(preState);
      runIsReachable = SafeResult.valueOf(res);
      if(!runIsReachable.isSafe()) return Pair.of(false, preState);
		}
  	
  	StateExpression currState = preState;
    for(IRStatement stmt : block.getStatements()) {
    	currState = encodeStatement(stmt, currState);
    	attachTraceExprToBlock(factory, block, stmt, pathEncoding.getTraceExpression());
    }
		return Pair.of(true, currState);
  }
	
	@Override
	public Pair<Boolean, StateExpression> encodeBlock(
			TraceFactory factory, 
			IRBasicBlock block, 
			StateExpression preState) 
					throws PathFactoryException {
  	
		processTraceNode(factory, block);
  	
  	StateExpression currState = preState;
    for(IRStatement stmt : block.getStatements()) { 
    	IOUtils.debug().pln("Encoding " + stmt.toString());
    	currState = encodeStatement(stmt, currState);
    	attachTraceExprToBlock(factory, block, stmt, pathEncoding.getTraceExpression());
    	
    	if(!runIsValid.isSafe())	return Pair.of(false, currState);
    	
    	if(stmt.getType().equals(StatementType.ASSERT)) {
    		ExpressionEncoder encoder = pathEncoding.getExpressionEncoder();
    		Expression pre = stmt.getPreCondition(currState, encoder);
    		boolean succeed = checkAssertion(currState, pre, stmt.toString());
    		if(!succeed) return Pair.of(succeed, currState); // return false to interrupt encoding
    	}
    }
    return Pair.of(true, currState);
  }

	@Override
	public boolean checkKeepUnroll() throws PathFactoryException {
		if(!checkKeepUnroll) return true;
		
		try {
			TheoremProver tp = pathEncoding.getExpressionManager().getTheoremProver();
			for(Expression assump : ImmutableSet.copyOf(keepUnrollMap.keySet())) {
				Collection<? extends IREdge<? extends IRBasicBlock>> edges 
						= keepUnrollMap.remove(assump);
				IOUtils.err().println("Checking keep unrolling at exit edges: " + edges);
				SatResult<?> sat = tp.checkSat(assump);
				if(!sat.isUnsatisfiable()) return true;
			}
			return false;
		} catch (TheoremProverException e) {
			throw new PathFactoryException(e);
		}
	}

	@Override
	public boolean checkExitUnroll() throws PathFactoryException {
		if(!checkExitUnroll) return false;
		
		try {
			TheoremProver tp = pathEncoding.getExpressionManager().getTheoremProver();
			for(Expression assump : ImmutableSet.copyOf(exitUnrollMap.keySet())) {
				Collection<? extends IREdge<? extends IRBasicBlock>> edges 
						= exitUnrollMap.remove(assump);
				IOUtils.err().println("Checking exit unrolling at loop exit edges: " + edges);
				ValidityResult<?> valid = tp.checkValidity(assump);
				if(!valid.isValid()) return true;
			}
			return false;
		} catch (TheoremProverException e) {
			throw new PathFactoryException(e);
		}
	}

	void preprocess(final PreProcessor<?> preprocessor, 
			IRControlFlowGraph cfg, 
			LoopInfo loopInfo, 
			boolean mergeLoopUnroll) throws PathFactoryException {
		if(preprocessor == null) return;
		
		BlockEncodingStrategy<Void> preprocessBlockStrategy = new BlockEncodingStrategy<Void>() {
			@Override
			public Pair<Boolean, Void> apply(IRBasicBlock block, Void preState) {
		    for(IRStatement stmt : block.getStatements()) {
					IOUtils.debug().pln("Preprocessing " + stmt);
		    	preprocessor.analysis(stmt);
		    }
				return Pair.of(true, null);
			}
		};
		
		EdgeEncodingStrategy<Void> preprocessEdgeStrategy = new EdgeEncodingStrategy<Void>() {
			@Override
			public Pair<Boolean, Void> apply(IREdge<?> edge, Void preState) {
				if(edge.getGuard() == null) return Pair.of(true, null);
				IRStatement assumeStmt = Statement.assumeStmt(edge.getSourceNode(), edge.getGuard());
				IOUtils.debug().pln("Preprocessing " + assumeStmt);
	    	preprocessor.analysis(assumeStmt);
	    	return Pair.of(true, null);
			}
		};
		
		PhiNodeResolveStrategy<Void> preprocessMergeStrategy = new PhiNodeResolveStrategy<Void>() {
			@Override
      public Void apply(Collection<Void> preStates) {
	      return null;
      }
		};
		
		TraceEncodeStrategy traceEncodeStrategy = new TraceEncodeStrategy() {
			@Override
			public void encode(IREdge<?> edge) {}
			
			@Override
			public void encode(IRBasicBlock block) {}
		};
		
		MemLeakCheckStrategy<Void> memLeakCheckStrategy = new MemLeakCheckStrategy<Void>() {
			@Override
      public void apply(Void state) throws PathFactoryException {
				return;
      }
		};
		
		statePropagateDFS(cfg, 
				loopInfo, 
				preprocessBlockStrategy, 
				preprocessEdgeStrategy, 
				preprocessMergeStrategy,
				traceEncodeStrategy,
				memLeakCheckStrategy,
				mergeLoopUnroll,
				false,
				false,
				null);
	  CScopeAnalyzer.reset();
	}

	private <T> boolean statePropagateDFSInLoop(IRControlFlowGraph cfg,
			LoopInfo loopInfo,
			BlockEncodingStrategy<T> blockStrategy,
			EdgeEncodingStrategy<T> edgeStrategy,
			PhiNodeResolveStrategy<T> mergeStrategy,
			TraceEncodeStrategy traceEncodeStrategy,
			final Map<IREdge<?>, T> edgeSrcStateMap,
			Loop loop,
			boolean checkExitUnroll, 
			boolean checkKeepUnroll, 
			T preLoopHeaderState) throws PathFactoryException {
		
		Collection<IRBasicBlock> blocksInExitRound = loop.getBlocksInExitRound();
		Collection<IRBasicBlock> blocksInLoopRound = loop.getBlocksInLoopRound();
		
		LoopCountDownLatch countDownLatch = loopCountDownLatchMap.get(loop);
		countDownLatch.reset();
		
		Deque<IRBasicBlock> propagateWorkList = Queues.newArrayDeque();
		propagateWorkList.push(loop.getHeader());
		
		while(!propagateWorkList.isEmpty()) {
			IRBasicBlock block = propagateWorkList.pop();
			
			T preState;
						
			if(block == loop.getHeader() && countDownLatch.notCountDownYet()) {
				/* The first time encode loop header */
				preState = preLoopHeaderState;
			} else {
				if(countDownLatch.stop()) {
					/* In the exit round, just visit the paths leads to exit edges */
					if(!blocksInExitRound.contains(block)) continue;
				} else {
					/* In the loop round, just visit the paths leads to back edges */
					if(!blocksInLoopRound.contains(block)) continue;
				}
				
				/* Resolve the phi-node to get the pre-state of current block */
				Pair<Boolean, T> preStatePair = getMergedPreState(cfg.getIncomingEdges(block), 
						edgeSrcStateMap, edgeStrategy, mergeStrategy);
				if(!preStatePair.fst()) return false;
				preState = preStatePair.snd();
			}
			
			Collection<? extends IREdge<? extends IRBasicBlock>> succEdges;
			
			boolean isNestLoopHeader = block != loop.getHeader() &&
					block == loopInfo.getInnerLoopMap().get(block).getHeader();
				
			if(isNestLoopHeader) { // nested loop header, recursive call
				Loop nestLoop = loopInfo.getInnerLoopMap().get(block);
				boolean funcQueryResult = statePropagateDFSInLoop(cfg, 
						loopInfo, 
						blockStrategy, 
						edgeStrategy,
						mergeStrategy,
						traceEncodeStrategy,
						edgeSrcStateMap,
						nestLoop, 
						checkExitUnroll,
						checkKeepUnroll, 
						preState);
				if(!funcQueryResult) return funcQueryResult;
				succEdges = nestLoop.getExitEdges();
				
				if(checkExitUnroll)	addExitUnrollAssumptions(succEdges, edgeSrcStateMap);
				if(checkKeepUnroll)	addKeepUnrollAssumptions(succEdges, edgeSrcStateMap);
				
			} else {
				traceEncodeStrategy.encode(block);
				Pair<Boolean, T> stateAndQueryResult = blockStrategy.apply(block, preState);
				
				boolean funcQueryResult = stateAndQueryResult.fst();
				T state = stateAndQueryResult.snd(); 
				if(!funcQueryResult) return funcQueryResult;
								
				/* Save exit-state for each exit edge of every round of loop unrolling 
				 * in the edge-src-state map, which is updated until reach the final 
				 * round of unrolling. Finally, the exit edge will be mapped to the 
				 * final round exit state */
				
				succEdges = cfg.getOutgoingEdges(block);
				for(IREdge<?> succEdge : succEdges) 
					edgeSrcStateMap.put(succEdge, state);
			}
	    
			/* Find all the successors of block could be pushed into the work list */
	    for(IREdge<?> succEdge : succEdges) {
	    	traceEncodeStrategy.encode(succEdge);
	    	
	    	/* skip all loop exit edges */
				if(loop.getExitEdges().contains(succEdge)) continue;
				
				IRBasicBlock succ = succEdge.getTarget();
				
				if(succ == loop.getHeader()) {
					/* Do not push loop header to work list if unroll is done */
					if(countDownLatch.stop()) continue;
					
					/* Do not push loop header to work list until all backEdges are encoded */
					boolean isReadyToWork = true;
					for(IREdge<?> backEdge : loop.getBackEdges()) {
						if(!edgeSrcStateMap.containsKey(backEdge)) {
							isReadyToWork = false; break;
						}
					}
					if(isReadyToWork) {
						countDownLatch.countDown();
						propagateWorkList.push(succ);
					}
					
				} else {
					boolean isSuccNestLoopHeader = loopInfo.getInnerLoopMap().containsKey(succ) && 
							succ == loopInfo.getInnerLoopMap().get(succ).getHeader();
					
					if(isSuccNestLoopHeader) {
						/* Do not add nested loop header to work list until all its incoming edges
						 * except back-edges are encoded and stored in edge-src-state-map
						 */
						Loop nestLoop = loopInfo.getInnerLoopMap().get(succ);
						final Collection<IREdge<?>> nestBackEdges = nestLoop.getBackEdges();
						boolean readyToWork = Iterables.all(cfg.getIncomingEdges(succ), 
								new Predicate<IREdge<?>>() {
									@Override
									public boolean apply(IREdge<?> edge) {
										// loop header ignore all back edges
										return nestBackEdges.contains(edge) || edgeSrcStateMap.containsKey(edge);
									}
						});
						
						if(readyToWork) propagateWorkList.push(succ);
						
					} else {
					
						/* Do not push successor to work list until all its incoming edges are 
						 * encoded and stored in edge-src-state-map
						 */
						boolean isReadyToWork = Iterables.all(cfg.getIncomingEdges(succ), 
								new Predicate<IREdge<?>>() {
									@Override
									public boolean apply(IREdge<?> edge) {
										return edgeSrcStateMap.containsKey(edge);
									}
						});
						
						if(isReadyToWork) propagateWorkList.push(succ);
					}
				}
	    }
		}		
		return true;
	}

	private <T> boolean statePropagateDFSInLoopMergeUnroll(IRControlFlowGraph cfg,
			LoopInfo loopInfo,
			BlockEncodingStrategy<T> blockStrategy,
			EdgeEncodingStrategy<T> edgeStrategy,
			PhiNodeResolveStrategy<T> mergeStrategy,
			TraceEncodeStrategy traceEncodeStrategy,
			final Map<IREdge<?>, T> edgeSrcStateMap,
			Loop loop,
			boolean checkExitUnroll, 
			boolean checkKeepUnroll, 
			T preLoopHeaderState) throws PathFactoryException {
		Collection<IRBasicBlock> blocksInExitRound = loop.getBlocksInExitRound();
		
		LoopCountDownLatch countDownLatch = loopCountDownLatchMap.get(loop);
		countDownLatch.reset();
		
		LoopUnrollMerger<T> merger = new LoopUnrollMerger<T>();
		
		Deque<IRBasicBlock> propagateWorkList = Queues.newArrayDeque();
		propagateWorkList.push(loop.getHeader());
		
		while(!propagateWorkList.isEmpty()) {
			IRBasicBlock block = propagateWorkList.pop();
			T preState;
			
			if(block == loop.getHeader() && countDownLatch.notCountDownYet()) {
				/* The first time encode loop header */
				preState = preLoopHeaderState;
			} else {
				
				if(countDownLatch.stop()) {
					/* In the exit round, just visit the paths leads to exit edges */
					if(!blocksInExitRound.contains(block)) continue;
				}
				
				/* Resolve the phi-node to get the pre-state of current block */
				Pair<Boolean, T> preStatePair = getMergedPreState(cfg.getIncomingEdges(block), 
						edgeSrcStateMap, edgeStrategy, mergeStrategy);
				if(!preStatePair.fst()) return false;
				preState = preStatePair.snd();
			}
			
			Collection<? extends IREdge<? extends IRBasicBlock>> succEdges;
			
			boolean isNestLoopHeader = block != loop.getHeader() &&
					block == loopInfo.getInnerLoopMap().get(block).getHeader();
				
			if(isNestLoopHeader) { // nested loop header, recursive call
				Loop nestLoop = loopInfo.getInnerLoopMap().get(block);
				boolean funcQueryResult = statePropagateDFSInLoopMergeUnroll(cfg, 
						loopInfo, 
						blockStrategy, 
						edgeStrategy,
						mergeStrategy,
						traceEncodeStrategy,
						edgeSrcStateMap,
						nestLoop, 
						checkExitUnroll,
						checkKeepUnroll, 
						preState);
				if(!funcQueryResult) return funcQueryResult;
				succEdges = nestLoop.getExitEdges();
				
				if(checkExitUnroll)	addExitUnrollAssumptions(succEdges, edgeSrcStateMap);
				if(checkKeepUnroll)	addKeepUnrollAssumptions(succEdges, edgeSrcStateMap);
				
			} else {
				traceEncodeStrategy.encode(block);
				Pair<Boolean, T> stateAndQueryResult = blockStrategy.apply(block, preState);
				
				boolean funcQueryResult = stateAndQueryResult.fst();
				T state = stateAndQueryResult.snd(); 
				if(!funcQueryResult) return funcQueryResult;
					
				/* Save exit-states for each exit edge of every round of loop unrolling 
				 * to merger, which will be merged when exit the current loop. Finally,
				 * the exit edge will be mapped to the merged exit state, and be saved
				 * in the edge-src-state-map */
				
				succEdges = cfg.getOutgoingEdges(block);	
				for(IREdge<?> succEdge: succEdges) {
					if(loop.getExitEdges().contains(succEdge)) {
						merger.saveExitEdgeState(succEdge, state);
					} else {
						edgeSrcStateMap.put(succEdge, state);
					}
				}
			}
	    
			/* Find all the successors of block could be pushed into the work list */
	    for(IREdge<?> succEdge : succEdges) {
				traceEncodeStrategy.encode(succEdge);
				
	    	/* skip all loop exit edges */
				if(loop.getExitEdges().contains(succEdge)) continue;
				
				IRBasicBlock succ = succEdge.getTarget();
				
				if(succ == loop.getHeader()) {
					/* Do not push loop header to work list if unroll is done */
					if(countDownLatch.stop()) continue;
					
					/* Do not push loop header to work list until all backEdges are encoded */
					boolean isReadyToWork = true;
					for(IREdge<?> backEdge : loop.getBackEdges()) {
						if(!edgeSrcStateMap.containsKey(backEdge)) {
							isReadyToWork = false; break;
						}
					}
					if(isReadyToWork) {
						countDownLatch.countDown(); // count-down the latch if all back-edges are encoded
						propagateWorkList.push(succ);
					}
					
				} else {
					boolean isSuccNestLoopHeader = loopInfo.getInnerLoopMap().containsKey(succ) && 
							succ == loopInfo.getInnerLoopMap().get(succ).getHeader();
					
					if(isSuccNestLoopHeader) {
						/* Do not add nested loop header to work list until all its incoming edges
						 * except back-edges are encoded and stored in edge-src-state-map
						 */
						Loop nestLoop = loopInfo.getInnerLoopMap().get(succ);
						final Collection<IREdge<?>> nestBackEdges = nestLoop.getBackEdges();
						boolean readyToWork = Iterables.all(cfg.getIncomingEdges(succ), 
								new Predicate<IREdge<?>>() {
									@Override
									public boolean apply(IREdge<?> edge) {
										
										/* clean the nest back edges if it's encoded (maybe in the last time encode the loop)
										 * back edges cannot be encoded before encode the nest loop
										 */
										
										if(nestBackEdges.contains(edge)) {
											edgeSrcStateMap.remove(edge);
											return true;
										} else {
											return edgeSrcStateMap.containsKey(edge);
										}
									}
						});
						
						if(readyToWork) propagateWorkList.push(succ);
						
					} else {
					
						/* Do not push successor to work list until all its incoming edges are 
						 * encoded and stored in edge-src-state-map
						 */
						boolean isReadyToWork = Iterables.all(cfg.getIncomingEdges(succ), 
								new Predicate<IREdge<?>>() {
									@Override
									public boolean apply(IREdge<?> edge) {
										return edgeSrcStateMap.containsKey(edge);
									}
						});
						
						if(isReadyToWork) propagateWorkList.push(succ);
					}
				}
	    }
		}
		
		// To merge exit-states of every round of loop unrolling
		Map<IREdge<?>, T> exitEdgeSrcStateMap = merger.getExitEdgeStateMap(edgeStrategy, mergeStrategy);
		edgeSrcStateMap.putAll(exitEdgeSrcStateMap);
		
		countDownLatch.reset();
		return true;
	}

	<T> void statePropagateDFS(IRControlFlowGraph cfg, 
			LoopInfo loopInfo,
			BlockEncodingStrategy<T> blockStrategy,
			EdgeEncodingStrategy<T> edgeStrategy,
			PhiNodeResolveStrategy<T> mergeStrategy,
			TraceEncodeStrategy traceEncodeStrategy,
			MemLeakCheckStrategy<T> memLeakCheckStrategy,
			boolean mergeLoopUnroll,
			boolean checkExitUnroll, 
			boolean checkKeepUnroll, 
			T initState) throws PathFactoryException {
		initLoopCountDownLatch(loopInfo);
		
		/* Map the edge to its source block's state */
		final Map<IREdge<?>, T> edgeSrcStateMap = Maps.newHashMap();
		
		Deque<IRBasicBlock> propagateWorkList = Queues.newArrayDeque();
		propagateWorkList.push(cfg.getEntry());
		
		T state = initState;
		
		while(!propagateWorkList.isEmpty()) {
			IRBasicBlock block = propagateWorkList.pop();
			
			T preState;
			if(block == cfg.getEntry()) { /* Encode the state for the entry block */
				preState = initState;
			} else {
				/* Resolve the phi-node to get the pre-state of current block */
				Pair<Boolean, T> preStatePair = getMergedPreState(cfg.getIncomingEdges(block), 
						edgeSrcStateMap, edgeStrategy, mergeStrategy);
				if(!preStatePair.fst()) return;
				preState = preStatePair.snd();
			}
			
			Collection<? extends IREdge<? extends IRBasicBlock>> succEdges;
			
			boolean isLoopHeader = loopInfo.getInnerLoopMap().containsKey(block) && 
					block == loopInfo.getInnerLoopMap().get(block).getHeader();
			if(isLoopHeader) { // loop header, call propagate state in loop
				Loop nestLoop = loopInfo.getInnerLoopMap().get(block);
				boolean funcQueryResult;
				if(mergeLoopUnroll) {
					funcQueryResult = statePropagateDFSInLoopMergeUnroll(cfg, 
						loopInfo, 
						blockStrategy, 
						edgeStrategy,
						mergeStrategy,
						traceEncodeStrategy,
						edgeSrcStateMap, 
						nestLoop, 
						checkExitUnroll,
						checkKeepUnroll, 
						preState);
				} else {
					funcQueryResult = statePropagateDFSInLoop(cfg, 
							loopInfo, 
							blockStrategy, 
							edgeStrategy,
							mergeStrategy,
							traceEncodeStrategy,
							edgeSrcStateMap, 
							nestLoop, 
							checkExitUnroll,
							checkKeepUnroll, 
							preState);
				}
				
				if(!funcQueryResult) return;
				
				succEdges = nestLoop.getExitEdges();
				
				if(checkExitUnroll)	addExitUnrollAssumptions(succEdges, edgeSrcStateMap);
				if(checkKeepUnroll)	addKeepUnrollAssumptions(succEdges, edgeSrcStateMap);
				
			} else {
				traceEncodeStrategy.encode(block);
				Pair<Boolean, T> stateAndQueryResult = blockStrategy.apply(block, preState);
				
				boolean funcQueryResult = stateAndQueryResult.fst();
				state = stateAndQueryResult.snd(); 
				if(!funcQueryResult) return;
				
				succEdges = cfg.getOutgoingEdges(block);
				
				for(IREdge<?> succEdge : succEdges) edgeSrcStateMap.put(succEdge, state);
			}
			
	    /* Find all the successors of block to add to the work list */
	    for(IREdge<?> outgoing : succEdges) {
				traceEncodeStrategy.encode(outgoing);
				
				IRBasicBlock succ = outgoing.getTarget();
				
				boolean isNestLoopHeader = loopInfo.getInnerLoopMap().containsKey(succ) && 
						succ == loopInfo.getInnerLoopMap().get(succ).getHeader();
				if(isNestLoopHeader) {
					/* Do not add nested loop header to work list until all its incoming edges
					 * except back-edges are encoded and stored in edge-src-state-map
					 */
					Loop nestLoop = loopInfo.getInnerLoopMap().get(succ);
					final Collection<IREdge<?>> nestBackEdges = nestLoop.getBackEdges();
					boolean readyToWork = Iterables.all(cfg.getIncomingEdges(succ), 
							new Predicate<IREdge<?>>() {
								@Override
								public boolean apply(IREdge<?> edge) {
									
									/* clean the nest back edges if it's encoded (maybe in the last time encode the loop)
									 * back edges cannot be encoded before encode the nest loop
									 */
									
									if(nestBackEdges.contains(edge)) {
										edgeSrcStateMap.remove(edge);
										return true;
									} else {
										return edgeSrcStateMap.containsKey(edge);
									}
								}
					});
					
					if(readyToWork) propagateWorkList.push(succ);
				} else {
					/* Do not add successor to work list until all its incoming edges are 
					 * encoded and stored in edge-src-state-map
					 */
					boolean readyToWork = Iterables.all(cfg.getIncomingEdges(succ), 
							new Predicate<IREdge<?>>() {
								@Override
								public boolean apply(IREdge<?> edge) {
									return edgeSrcStateMap.containsKey(edge);
								}
					});
					
					if(readyToWork) propagateWorkList.push(succ);
				}
	    }
		}
		
		memLeakCheckStrategy.apply(state);
	}

	/** Encode statement stmt, with single pre-condition 
		 * @throws PathFactoryException */
	StateExpression encodeStatement(IRStatement stmt, StateExpression preCondition) 
			throws PathFactoryException {
		/* Precondition is OK, encode the postcondition. */
//		IOUtils.out().println(stmt.getLocation() + " " + stmt); 
		pathEncoding.reset();
		
		StateExpression postCond = getPostCondition(preCondition, stmt);
		
		if(pathEncoding.preRunIsValid() != null) {
			runIsValid = SafeResult.valueOf(pathEncoding.preRunIsValid());
			runIsValid.setFailReason(pathEncoding.getFailReason());
		}
		return postCond;
	}
		
	/**
	 * Check the <code>assertion</code> with current state <code>preCond</code>
	 * 
	 * @param preCond
	 *          the current state
	 * @param assertion
	 * 
	 * @param failReason
	 * 
	 * @return false if the assertion results in an invalid verification condition
	 *         or an infeasible path; true otherwise.
	 */
	boolean checkAssertion(StateExpression preCond, Expression assertion, String failReason) 
	    throws PathFactoryException {
		/* If the statement has a precondition, we have to check it before continuing with 
		 * the encoding.
		 */
	    //		IOUtils.debug().pln("Checking assertion: " + assertion).flush();
		ValidityResult<?> result = pathEncoding.checkAssertion(preCond, assertion);
		runIsValid = SafeResult.valueOf(result);
		
		if (!runIsValid.isSafe()) {
			runIsValid.setFailReason(failReason); return false;
		}
		
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

	private StateExpression getPostCondition(StateExpression prefix, IRStatement stmt) 
			throws PathFactoryException {
		switch (stmt.getType()) {
		case DECLARE:
			if(stmt.hasPreLabel(Identifiers.STATIC)) {
				if(staticStmts.contains(stmt)) break;
				staticStmts.add(stmt);
			}
			return pathEncoding.declare(prefix, stmt.getOperand(0)); 
		case INIT:{
			if(stmt.hasPreLabel(Identifiers.STATIC)) {
				if(staticStmts.contains(stmt)) break;
				staticStmts.add(stmt);
			}
			int size = stmt.getOperands().size();
			IRExpression[] operands = new IRExpression[size-1];
			stmt.getOperands().subList(1, size).toArray(operands);
			return pathEncoding.init(prefix, stmt.getOperand(0), operands);
		}
		case ASSIGN:
			return pathEncoding.assign(prefix, stmt.getOperand(0), stmt.getOperand(1));
		case ASSUME:
			return pathEncoding.assume(prefix, stmt.getOperand(0));
		case MALLOC:
			return pathEncoding.malloc(prefix, stmt.getOperand(0), stmt.getOperand(1));
		case CALLOC:
			return pathEncoding.calloc(prefix, stmt.getOperand(0), stmt.getOperand(1), stmt.getOperand(2));
		case ALLOCA:
			return pathEncoding.alloca(prefix, stmt.getOperand(0), stmt.getOperand(1));
		case FREE:
			return pathEncoding.free(prefix, stmt.getOperand(0));
		case HAVOC:
			return pathEncoding.havoc(prefix, stmt.getOperand(0));
		case FUNC_ENT:
			String scopeName = CType.getScopeName(stmt.getSourceNode());
			CScopeAnalyzer.pushScope(scopeName);
			break;
		case FUNC_EXIT:
			CScopeAnalyzer.popScope();
			break;
		case CALL: {
			int size = stmt.getOperands().size();
			IRExpression[] operands = new IRExpression[size-1];
			stmt.getOperands().subList(1, size).toArray(operands);
			return pathEncoding.call(prefix, stmt.getOperand(0), operands);
		}
		case RETURN: {
			if(stmt.getOperands().size() == 1)
				return pathEncoding.ret(prefix, stmt.getOperand(0));
		}
		case SKIP:	
		default:
			IOUtils.debug().pln(
					"Statement.getPostCondition: Ignoring statement type: "
							+ stmt.getType());
		}
		
		return pathEncoding.noop(prefix);
	}

	private void attachTraceExprToEdge(TraceFactory factory, IREdge<?> edge,
			IRStatement stmt, Expression traceExpr) {
		if(!Preferences.isSet(Preferences.OPTION_TRACE)) return;
		IRTraceNode traceNode = factory.getTraceNode(edge);
		traceNode.addStatements(Collections.singleton(stmt));
		traceNode.setStmtTraceExpr(stmt, traceExpr);
	}

	private void processTraceNode(TraceFactory factory, IRBasicBlock block) {
		if(!Preferences.isSet(Preferences.OPTION_TRACE)) return;
		IRTraceNode traceNode = factory.getTraceNode(block);
		traceNode.addLabels(block.getPreLabels());
		traceNode.addStatements(block.getStatements());
	}

	private void attachTraceExprToBlock(TraceFactory factory, IRBasicBlock block, 
			IRStatement stmt, Expression traceExpr) {
		if(!Preferences.isSet(Preferences.OPTION_TRACE)) return;
		IRTraceNode traceNode = factory.getTraceNode(block);
		traceNode.setStmtTraceExpr(stmt, traceExpr);
	}

	private void initLoopCountDownLatch(LoopInfo loopInfo) {
		Deque<Loop> loopWorkList = Queues.newArrayDeque();
		loopWorkList.addAll(loopInfo.getTopLevelLoops());
		
		/* In-order traverse */
		while(!loopWorkList.isEmpty()) {
			Loop loop = loopWorkList.pop();
			loopWorkList.addAll(loop.getSubLoops());
			loopCountDownLatchMap.put(loop, new LoopCountDownLatch(iterTimes));
		}
	}

	private <T> Pair<Boolean, T> getMergedPreState(
			Iterable<? extends IREdge<? extends IRBasicBlock>> incomingEdges, 
			final Map<IREdge<? extends IRBasicBlock>, T> edgeSrcStateMap,
			EdgeEncodingStrategy<T> edgeStrategy,
			PhiNodeResolveStrategy<T> mergeStrategy) throws PathFactoryException {
		
		Collection<T> preStates = Lists.newArrayListWithExpectedSize(Iterables.size(incomingEdges));
		
		for(IREdge<? extends IRBasicBlock> incoming : incomingEdges) {
			if(!edgeSrcStateMap.containsKey(incoming))  continue;
			
			/* Get the src-state, and remove the edge for future propagation 
			 * in next round loop-unrolling */
			T srcState = edgeSrcStateMap.remove(incoming);
			Pair<Boolean, T> stateAndQueryResult = edgeStrategy.apply(incoming, srcState);
			boolean funcQueryResult = stateAndQueryResult.fst();
			T state = stateAndQueryResult.snd(); 
			if(!funcQueryResult) return Pair.of(funcQueryResult, null);
			preStates.add(state);
		}
		
		T preState = mergeStrategy.apply(preStates);
		return Pair.of(true, preState);
	}
	
	private <T> void addExitUnrollAssumptions(
			Collection<? extends IREdge<? extends IRBasicBlock>> exitEdges, 
			Map<IREdge<?>, T> edgeSrcStateMap) {
		ImmutableList.Builder<Expression> builder = new ImmutableList.Builder<Expression>();
		ExpressionEncoder encoder = pathEncoding.getExpressionEncoder();
		for(IREdge<? extends IRBasicBlock> exitEdge : exitEdges) {
			assert(edgeSrcStateMap.containsKey(exitEdge));
			StateExpression srcState = (StateExpression) edgeSrcStateMap.get(exitEdge);
	  	Expression loopExitGuard = exitEdge.getGuard().toBoolean(srcState, encoder);
	  	BooleanExpression exitUnrollAssump = pathEncoding.pathToBoolean(srcState).implies(loopExitGuard);
	  	builder.add(exitUnrollAssump);
		}
		Expression exitUnroll = pathEncoding.getExpressionEncoding().or(builder.build());
		exitUnrollMap.put(exitUnroll, exitEdges);
	}
	
	private <T> void addKeepUnrollAssumptions(
			Collection<? extends IREdge<? extends IRBasicBlock>> exitEdges, 
			Map<IREdge<? extends IRBasicBlock>, T> edgeSrcStateMap) {
		ImmutableList.Builder<BooleanExpression> builder = new ImmutableList.Builder<BooleanExpression>();
		ExpressionEncoder encoder = pathEncoding.getExpressionEncoder();
		for(IREdge<?> exitEdge : exitEdges) {
			assert(edgeSrcStateMap.containsKey(exitEdge));
			StateExpression srcState = (StateExpression) edgeSrcStateMap.get(exitEdge);
	  	Expression loopExitGuard = exitEdge.getGuard().toBoolean(srcState, encoder);
	  	BooleanExpression unrollAssump = pathEncoding.pathToBoolean(srcState)
	  			.implies(loopExitGuard);
	  	builder.add(unrollAssump.not());
		}
		
		Expression keepUnroll = pathEncoding.getExpressionEncoding().or(builder.build());
		keepUnrollMap.put(keepUnroll, exitEdges);
	}
}