package edu.nyu.cascade.c.encoder;

import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.SafeResult;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRTraceNode;
import edu.nyu.cascade.ir.IRStatement.StatementType;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.impl.LoopInfo;
import edu.nyu.cascade.ir.impl.Statement;
import edu.nyu.cascade.ir.impl.TraceFactory;
import edu.nyu.cascade.ir.path.PathEncoding;
import edu.nyu.cascade.ir.path.PathFactoryException;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;
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

	private final StmtBasedFormulaEncoder stmtFormulaEncoder;
	private final Map<IRBasicBlock, StateExpression> cleanBlockStateClosureMap;
	private final Map<IREdge<?>, StateExpression> cleanEdgeStateMap;
	private final Map<VariableExpression, VariableExpression> varsFreshMap;
	private final PathEncoding pathEncoding;
	private final StateFactory<?> stateFactory;
	private SafeResult runIsValid, runIsReachable;
	private boolean checkFeasibility;
	private boolean checkExitUnroll, checkKeepUnroll;
	private int iterTimes;

	private BlockBasedFormulaEncoder(PathEncoding pathEncoding,
			TraceFactory traceFactory) {
		this.pathEncoding = pathEncoding;
		stateFactory = pathEncoding.getStateFactory();
		stmtFormulaEncoder = StmtBasedFormulaEncoder.create(pathEncoding,
				traceFactory);
		cleanBlockStateClosureMap = Maps.newHashMap();
		cleanEdgeStateMap = Maps.newHashMap();
		varsFreshMap = Maps.newLinkedHashMap();
		reset();
	}

	public static BlockBasedFormulaEncoder create(PathEncoding encoding,
			TraceFactory traceFactory) {
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
		this.iterTimes = iterTimes;
		stmtFormulaEncoder.setIterTimes(iterTimes);
	}

	@Override
	public void reset() {
		checkFeasibility = false;
		checkExitUnroll = false;
		checkKeepUnroll = false;
		runIsValid = SafeResult.valid();
		runIsReachable = SafeResult.valid();
		cleanBlockStateClosureMap.clear();
		cleanEdgeStateMap.clear();
		varsFreshMap.clear();
		stmtFormulaEncoder.reset();
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
	public void encode(final IRControlFlowGraph cfg, LoopInfo loopInfo)
			throws PathFactoryException {

		final TraceFactory factory = new TraceFactory();

		BlockEncodingStrategy<StateExpression> blockStrategy = new BlockEncodingStrategy<StateExpression>() {
			@Override
			public Pair<Boolean, StateExpression> apply(IRBasicBlock block,
					StateExpression preState) throws PathFactoryException {
				return encodeBlock(factory, block, preState);
			}
		};

		EdgeEncodingStrategy<StateExpression> edgeStrategy = new EdgeEncodingStrategy<StateExpression>() {
			@Override
			public Pair<Boolean, StateExpression> apply(IREdge<?> edge,
					StateExpression preState) throws PathFactoryException {
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
				if (!Preferences.isSet(Preferences.OPTION_TRACE))
					return;
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
				if (!Preferences.isSet(Preferences.OPTION_MEMORY_CHECK))
					return;
				ExpressionManager exprManager = pathEncoding.getExpressionManager();

				Expression memory_no_leak = stateFactory.applyMemoryTrack(state);
				if (memory_no_leak.equals(exprManager.tt()))
					return;

				BooleanExpression query = stateFactory.stateToBoolean(state).implies(
						memory_no_leak);
				checkAssertion(query, Identifiers.VALID_MEMORY_TRACE);
			}
		};

		stmtFormulaEncoder.initLoopCountDownLatch(loopInfo, iterTimes);

		stmtFormulaEncoder.statePropagateDFS(cfg, loopInfo, blockStrategy,
				edgeStrategy, mergeStrategy, traceEncodeStrategy, memLeakCheckStrategy,
				checkExitUnroll, checkKeepUnroll, pathEncoding.emptyState());
		CScopeAnalyzer.reset();
	}

	@Override
	public void checkReach(IRControlFlowGraph cfg, LoopInfo loopInfo,
			final String label) throws PathFactoryException {

		final TraceFactory factory = new TraceFactory();

		BlockEncodingStrategy<StateExpression> blockStrategy = new BlockEncodingStrategy<StateExpression>() {
			@Override
			public Pair<Boolean, StateExpression> apply(IRBasicBlock block,
					StateExpression preState) throws PathFactoryException {
				return checkReachBlock(factory, block, preState, label);
			}
		};

		EdgeEncodingStrategy<StateExpression> edgeStrategy = new EdgeEncodingStrategy<StateExpression>() {
			@Override
			public Pair<Boolean, StateExpression> apply(IREdge<?> edge,
					StateExpression preState) throws PathFactoryException {
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
				if (!Preferences.isSet(Preferences.OPTION_TRACE))
					return;
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
				if (!Preferences.isSet(Preferences.OPTION_TRACE))
					return;
				factory.create(block);
			}
		};

		MemLeakCheckStrategy<StateExpression> memLeakCheckStrategy = new MemLeakCheckStrategy<StateExpression>() {
			@Override
			public void apply(StateExpression state) throws PathFactoryException {
				return;
			}
		};

		stmtFormulaEncoder.initLoopCountDownLatch(loopInfo, iterTimes);

		stmtFormulaEncoder.statePropagateDFS(cfg, loopInfo, blockStrategy,
				edgeStrategy, mergeStrategy, traceEncodeStrategy, memLeakCheckStrategy,
				checkExitUnroll, checkKeepUnroll, pathEncoding.emptyState());

		CScopeAnalyzer.reset();
	}

	@Override
	public Pair<Boolean, StateExpression> checkReachBlock(TraceFactory factory,
			IRBasicBlock block, StateExpression preState, String label)
			throws PathFactoryException {

		if (block.getPreLabels().contains(label)) {
			SatResult<?> res = pathEncoding.checkPath(preState);
			runIsReachable = SafeResult.valueOf(res);
			if (!runIsReachable.isSafe())
				return Pair.of(false, preState);
		}

		// FIXME: how to add statement to trace node
		StateExpression postState = getBlockState(block);
		stateFactory.propagateState(postState, preState);
		return Pair.of(true, postState);
	}

	@Override
	public Pair<Boolean, StateExpression> encodeEdge(TraceFactory factory,
			IREdge<?> edge, StateExpression preState) throws PathFactoryException {
		if (edge.getGuard() == null)
			return Pair.of(true, preState);

		// FIXME: how to add statement to trace node
		StateExpression postState = getEdgeState(edge);
		stateFactory.propagateState(postState, preState);

		Multimap<String, BooleanExpression> assertions = postState.getAssertions();
		for (Entry<String, BooleanExpression> entry : assertions.entries()) {
			String failReason = entry.getKey();
			BooleanExpression assertion = entry.getValue();
			boolean succeed = checkAssertion(assertion, failReason);
			if (!succeed)
				return Pair.of(succeed, postState); // return false to interrupt
																						// encoding
		}

		assertions.clear();
		return Pair.of(true, postState);
	}

	@Override
	public Pair<Boolean, StateExpression> encodeBlock(TraceFactory factory,
			IRBasicBlock block, StateExpression preState)
			throws PathFactoryException {
		StateExpression postState = getBlockState(block);
		stateFactory.propagateState(postState, preState);

		Multimap<String, BooleanExpression> assertions = postState.getAssertions();
		for (Entry<String, BooleanExpression> entry : assertions.entries()) {
			String failReason = entry.getKey();
			BooleanExpression assertion = entry.getValue();
			boolean succeed = checkAssertion(assertion, failReason);
			if (!succeed)
				return Pair.of(succeed, postState); // return false to interrupt
																						// encoding
		}

		assertions.clear();
		return Pair.of(true, postState);
	}

	@Override
	public IRTraceNode getErrorTrace(IRControlFlowGraph cfg) {
		return stmtFormulaEncoder.getErrorTrace(cfg);
	}

	/**
	 * Get the state closure for <code>block</code>, if <code>
	 * cleanBlockStateClosureMap</code> has it, just return the related state
	 * closure
	 * 
	 * @param block
	 * @return the clean state of block
	 * @throws PathFactoryException
	 */
	private StateExpression getBlockState(IRBasicBlock block)
			throws PathFactoryException {

		if (cleanBlockStateClosureMap.containsKey(block)) {
			StateExpression state = cleanBlockStateClosureMap.get(block);
			StateExpression stateCopy = stateFactory.copy(state);

			Collection<VariableExpression> fromElems = Lists.newArrayList();
			Collection<VariableExpression> toElems = Lists.newArrayList();

			collectFreshRegions(state, fromElems, toElems);

			collectFreshVars(state);

			fromElems.addAll(varsFreshMap.keySet());
			toElems.addAll(varsFreshMap.values());

			stateFactory.substitute(stateCopy, fromElems, toElems);
			return stateCopy;
		}

		StateExpression postState = pathEncoding.emptyState();

		for (IRStatement stmt : block.getStatements()) {
			IOUtils.debug().pln("Encoding: " + stmt);
			postState = stmtFormulaEncoder.getPostCondition(postState, stmt);
			if (StatementType.ASSERT.equals(stmt.getType())) {
				ExpressionEncoder exprEncoder = pathEncoding.getExpressionEncoder();
				Expression assertion = stmt.getPreCondition(postState, exprEncoder);
				BooleanExpression query = stateFactory.stateToBoolean(postState)
						.implies(assertion);
				postState.addAssertion(stmt.toString(), query);
			}
		}

		cleanBlockStateClosureMap.put(block, postState);
		StateExpression stateCopy = stateFactory.copy(postState);
		stateFactory.substitute(stateCopy, varsFreshMap.keySet(), varsFreshMap
				.values());
		return stateCopy;
	}

	/**
	 * Get the clean state closure for <code>edge</code>, if <code>
	 * cleanEdgeStateClosureMap</code> stored it, just return the related state
	 * closure
	 * 
	 * @param edge
	 * @return the clean state closure of edge
	 * @throws PathFactoryException
	 */
	private StateExpression getEdgeState(IREdge<?> edge)
			throws PathFactoryException {
		if (cleanEdgeStateMap.containsKey(edge)) {
			StateExpression state = cleanEdgeStateMap.get(edge);
			StateExpression stateCopy = stateFactory.copy(state);
			stateFactory.substitute(stateCopy, varsFreshMap.keySet(), varsFreshMap
					.values());
			return stateCopy;
		}

		StateExpression emptyState = pathEncoding.emptyState();
		IRStatement assumeStmt = Statement.assumeStmt(edge.getSourceNode(), edge
				.getGuard(), true);
		IOUtils.debug().pln("Encoding: " + assumeStmt);

		StateExpression state = stmtFormulaEncoder.getPostCondition(emptyState,
				assumeStmt);
		cleanEdgeStateMap.put(edge, state);
		StateExpression stateCopy = stateFactory.copy(state);
		stateFactory.substitute(stateCopy, varsFreshMap.keySet(), varsFreshMap
				.values());
		return stateCopy;
	}

	/**
	 * Check the <code>query</code> with fail reason <code>failReason</code>
	 * 
	 * @param query
	 * @param failReason
	 * 
	 * @return false if the assertion results in an invalid verification condition
	 *         or an infeasible path; true otherwise.
	 */
	private boolean checkAssertion(Expression query, String failReason)
			throws PathFactoryException {
		/*
		 * If the statement has a precondition, we have to check it before
		 * continuing with the encoding.
		 */
		IOUtils.debug().pln("Checking assertion: " + query).flush();
		ValidityResult<?> result = pathEncoding.checkAssertion(query);
		runIsValid = SafeResult.valueOf(result);

		if (!runIsValid.isSafe()) {
			runIsValid.setFailReason(failReason);
			return false;
		}

		if (checkFeasibility)
			IOUtils.out().println("Cannot checking path feasibility with "
					+ "block based encoding");

		return true;
	}

	/**
	 * Generate fresh variables for re-visit block's local variables
	 * 
	 * @param state
	 */
	private void collectFreshVars(StateExpression state) {
		ExpressionManager exprManager = pathEncoding.getExpressionManager();
		ExpressionEncoding encoding = pathEncoding.getExpressionEncoding();
		for (VariableExpression var : state.getVars()) {
			VariableExpression freshVar = exprManager.variable(var.getName(), var
					.getType(), true);
			freshVar.setHoareLogic(var.isHoareLogic());
			varsFreshMap.put(var, freshVar);

			if (var.isHoareLogic()) {
				VariableExpression rvalBindingVar = encoding.getRvalBinding(var);
				VariableExpression rvalBidningFreshVar = encoding.getRvalBinding(
						freshVar);
				varsFreshMap.put(rvalBindingVar, rvalBidningFreshVar);
			}
		}
	}

	/**
	 * Generate fresh variables for re-visit block's fresh regions
	 * 
	 * @param state
	 */
	private void collectFreshRegions(StateExpression state,
			Collection<VariableExpression> fromElems,
			Collection<VariableExpression> toElems) {
		if (state.getRegions().isEmpty())
			return;

		ExpressionManager exprManager = pathEncoding.getExpressionManager();
		for (VariableExpression region : state.getRegions()) {
			String name = region.getName();
			Type type = region.getType();
			VariableExpression freshRegion = exprManager.variable(name, type, true);
			fromElems.add(region);
			toElems.add(freshRegion);
		}
	}
}
