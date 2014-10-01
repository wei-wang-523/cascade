package edu.nyu.cascade.c;

import java.util.Collection;

import com.google.common.collect.Table;

import edu.nyu.cascade.control.Position;
import edu.nyu.cascade.control.Run;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;

public interface RunProcessor<T> {
	
	void enableFeasibilityChecking();
  
  /**
   * Process a run: build the path through the CFG that it represents, convert
   * the path to a verification condition, then check the verification
   * condition.
   * 
   * @param run
   *          a run from a Cascade control file
   * @return true if all assertions in the run hold, false otherwise.
   * @throws RunProcessorException
   *           if an error occurred while processing the run. E.g., if the path
   *           was ill-defined, or if an unhandled statement was encountered.
   */
	boolean process(Run run) throws RunProcessorException;
	
  /**
	 * Process reachability checking in CFG to visit block with <code>label</code>
	 * 
	 * @param mainCfg
	 * @param label
	 * 
	 * @return true if it's reachable
   * @throws RunProcessorException 
	 */
	boolean processReachability(IRControlFlowGraph mainCfg, String label)
			throws RunProcessorException;
	
  /**
	 * Process reachability checking in CFG to visit block with <code>label</code>,
	 * incrementally until reach the loop iteration bound
	 * 
	 * @param mainCfg
	 * @param label
	 * 
	 * @return table records the result for every loop unrolling and function inlining
   * @throws RunProcessorException 
	 */
	Table<Integer, Integer, Boolean> processReachabilityIncremental(
			IRControlFlowGraph mainCfg, String label)
					throws RunProcessorException;

	T processCfg(IRControlFlowGraph cfg, Collection<Position> waypoints)
			throws RunProcessorException;

  /**
	 * Process run between blocks: <code>startBlock</code>, <code>endBlock</code> 
	 * and <code>waypoints</code>
	 * @param startBlock
	 * @param endBlock
	 * @param waypoints
	 * @param cfg
	 * @return
	 * @throws RunProcessorException
	 */
	T processRunBtwnBlocks(IRBasicBlock startBlock,
			IRBasicBlock endBlock, Collection<Position> waypoints,
			IRControlFlowGraph cfg, CSymbolTable symbolTable)
			throws RunProcessorException;
}