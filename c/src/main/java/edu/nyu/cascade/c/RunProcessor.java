package edu.nyu.cascade.c;

import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.impl.LoopInfo;

public interface RunProcessor {

	void enableFeasibilityChecking();

	boolean prepare(IRControlFlowGraph mainCfg);

	/**
	 * Simplify and pre-process the cfgs
	 */
	void init();

	void init(String label);

	void preprocess();

	/**
	 * Process reachability checking in CFG to visit block with <code>label</code>
	 * 
	 * @return true if the labeled block are unreachable
	 * @throws RunProcessorException
	 */
	SafeResult processReachability(IRControlFlowGraph mainCfg, LoopInfo loopInfo,
	    String label, int iterTime) throws RunProcessorException;

	/**
	 * Process assertion checking in CFG
	 * 
	 * @return true if all assertions are valid
	 * @throws RunProcessorException
	 */
	SafeResult processAssertion(IRControlFlowGraph mainCFG, LoopInfo loopInfo,
	    int iterTime) throws RunProcessorException;

	void dumpErrorTrace(IRControlFlowGraph cfg);

	void reset();

	boolean checkKeepUnroll() throws RunProcessorException;

	boolean checkExitUnroll() throws RunProcessorException;

	void enableCheckKeepUnroll();

	void enableCheckExitUnroll();

	boolean isFullyFuncInlined(IRControlFlowGraph mainCfg);
}