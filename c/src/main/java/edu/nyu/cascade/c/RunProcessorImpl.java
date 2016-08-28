package edu.nyu.cascade.c;

import java.util.List;
import java.util.Map;

import xtc.tree.Node;

import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import edu.nyu.cascade.c.encoder.BlockBasedFormulaEncoder;
import edu.nyu.cascade.c.encoder.FormulaEncoder;
import edu.nyu.cascade.c.encoder.StmtBasedFormulaEncoder;
import edu.nyu.cascade.c.mode.Mode;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.SymbolTable;
import edu.nyu.cascade.ir.expr.ExpressionEncoder;
import edu.nyu.cascade.ir.impl.LoopInfo;
import edu.nyu.cascade.ir.impl.TraceFactory;
import edu.nyu.cascade.ir.pass.IRAliasAnalyzer;
import edu.nyu.cascade.ir.path.PathFactoryException;
import edu.nyu.cascade.ir.path.SimplePathEncoding;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;
import edu.nyu.cascade.util.Pair;
import edu.nyu.cascade.util.Preferences;
import edu.nyu.cascade.util.ReservedFunction;

/**
 * A processor for control file runs. It is statement-based. For loop point and
 * function call point, we handle them separately. Create a loop graph for every
 * loop point, and create a function in-line graph for every path contains call
 * statement. In-line them into the original graph.
 */
class RunProcessorImpl implements RunProcessor {
	private RunProcessorImpl(Mode mode, SymbolTable symbolTable,
			Map<Node, IRControlFlowGraph> cfgMap, FunctionCallGraph callGraph) {
		this.mode = mode;
		this.traceFactory = new TraceFactory();

		this.globalCFG = Iterables.find(cfgMap.values(),
				new Predicate<IRControlFlowGraph>() {
					@Override
					public boolean apply(IRControlFlowGraph cfg) {
						return Identifiers.GLOBAL_CFG.equals(cfg.getName());
					}
				});

		this.cfgs = Lists.newArrayList(cfgMap.values());
		cfgs.remove(globalCFG);

		ExpressionEncoder encoder = CExpressionEncoder.create(mode);

		/* Build the preprocessor */
		preprocessor = mode.buildPreprocessor(symbolTable);

		formulaEncoder = Preferences.isSet(Preferences.OPTION_SBE)
				? BlockBasedFormulaEncoder.create(SimplePathEncoding.create(encoder),
						traceFactory)
				: StmtBasedFormulaEncoder.create(SimplePathEncoding.create(encoder),
						traceFactory);
		funcProcessor = FuncInlineProcessor.create(cfgMap, symbolTable,
				preprocessor);
		withNoMemAlloc = callGraph.getCallers(ReservedFunction.MALLOC).isEmpty()
				&& callGraph.getCallers(ReservedFunction.CALLOC).isEmpty();
	}

	static RunProcessorImpl create(Mode mode, SymbolTable symbolTable,
			Map<Node, IRControlFlowGraph> cfgs, FunctionCallGraph callGraph) {
		return new RunProcessorImpl(mode, symbolTable, cfgs, callGraph);
	}

	private final IRControlFlowGraph globalCFG;
	private final List<IRControlFlowGraph> cfgs;
	private final boolean withNoMemAlloc;
	private final FormulaEncoder formulaEncoder;
	private final FuncInlineProcessor<?> funcProcessor;
	private final IRAliasAnalyzer<?> preprocessor;
	private final Mode mode;
	private final TraceFactory traceFactory;

	@Override
	public void enableFeasibilityChecking() {
		formulaEncoder.setFeasibilityChecking(true);
	}

	@Override
	public boolean prepare(IRControlFlowGraph mainCfg) {
		/* Function in-line */
		boolean changed = funcProcessor.functionInlineCFG(mainCfg);

		/* Append global graph into graph */
		CfgProcessor.appendPreCFG(globalCFG, mainCfg);

		/* Path-based normalization */
		pathBasedNormalization(mainCfg);

		mainCfg.format(IOUtils.debug());
		return changed;
	}

	@Override
	public boolean isFullyFuncInlined(IRControlFlowGraph mainCfg) {
		return funcProcessor.hasFunctionCall(mainCfg);
	}

	@Override
	public SafeResult processAssertion(IRControlFlowGraph mainCFG,
			LoopInfo loopInfo, int iterTime) throws RunProcessorException {
		try {
			/* Set the iteration time */
			formulaEncoder.setIterTimes(iterTime);

			if (Preferences.isSet(Preferences.OPTION_TWOROUND_MEMCHECK)) {
				if (!withNoMemAlloc) {
					Preferences.set(Preferences.OPTION_MEMTRACK);
					formulaEncoder.encode(mainCFG, loopInfo);
					SafeResult result = formulaEncoder.runIsValid();
					if (result.isUnsafe())
						return result;

					reset();
				}
				Preferences.clearPreference(Preferences.OPTION_MEMTRACK);
				formulaEncoder.encode(mainCFG, loopInfo);
				return formulaEncoder.runIsValid();
			} else {
				formulaEncoder.encode(mainCFG, loopInfo);
				return formulaEncoder.runIsValid();
			}

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

			formulaEncoder.checkReach(mainCFG, loopInfo, label);
			return formulaEncoder.runIsReachable();

		} catch (PathFactoryException e) {
			throw new RunProcessorException(e);
		}
	}

	@Override
	public void dumpErrorTrace(IRControlFlowGraph cfg) {
		return;
	}

	@Override
	public void reset() {
		formulaEncoder.reset();
		traceFactory.reset();
		if (preprocessor != null)
			preprocessor.reset();
	}

	private boolean pathBasedNormalization(IRControlFlowGraph mainCFG) {
		return false;
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

	@Override
	public void preprocess() {
		if (preprocessor == null)
			return;
		if (!mode.hasPreprocessor())
			return;
		preprocessor.analysis(globalCFG, cfgs);
	}

	@Override
	public Pair<Integer, Integer> getAliasAnalysisStats() {
		return preprocessor.getAliasAnalysisStats(globalCFG, cfgs);
	}

	@Override
	public void init() {
		CfgProcessor.simplifyCFG(globalCFG);
		for (IRControlFlowGraph cfg : cfgs)
			CfgProcessor.simplifyCFG(cfg);
	}

	@Override
	public void init(String label) {
		CfgProcessor.simplifyCFG(globalCFG, label);

		for (IRControlFlowGraph cfg : cfgs)
			CfgProcessor.simplifyCFG(cfg, label);
	}
}