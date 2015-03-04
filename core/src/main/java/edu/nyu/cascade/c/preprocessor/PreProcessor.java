package edu.nyu.cascade.c.preprocessor;

import java.util.Collection;
import java.util.Map;

import xtc.tree.Node;

import com.google.common.collect.Range;

import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.prover.Expression;

/**
 * Pre-analysis statement
 * @author Wei
 *
 */
public interface PreProcessor<T> {	
  /**
   * Display the snap shot
   */
	String displaySnapShot();

	void buildSnapShot();

	T getPointsToLoc(T rep);
	
	long getRepTypeWidth(T rep);

	String getRepId(T rep);

	T getRep(Node node);
	
	/**
	 * Get the field representative of <code>rep</code>. It's
	 * used to in field-sensitive steensgaard analysis, to find 
	 * the elements' representative for the structure components
	 * 
	 * @param rep
	 * @return
	 */
	Collection<T> getFillInReps(T rep);

	/**
	 * Analysis control flow graph <code>cfg</code>
	 * @param stmt
	 */
	void analysis(IRControlFlowGraph cfg);

	/**
	 * Add an newly allocated <code>region</code> with source node 
	 * <code>ptrNode</code>
	 * @param region
	 * @param ptrNode
	 * @return
	 */
	void addAllocRegion(Expression region, Node ptrNode);

	/**
	 * Add a stack variable with expression <code>lval</code>,
	 * with source node <code>lvalNode</code>
	 * @param lval
	 * @param lvalNode
	 */
	void addStackVar(Expression lval, Node lvalNode);
	
	/**
	 * Get the mapping from offset to ECR in structure ECR
	 * only used for field-sensitive analysis
	 * 
	 * @param rep
	 * @return
	 */
	Map<Range<Long>, T> getStructMap(T rep);

	Collection<IRVar> getEquivFuncVars(Node funcNode);

	void reset();

	boolean isAccessTypeSafe(T rep);

	/**
	 * Perform value-flow analysis on <code>CFG</code>,
	 * return the value flow graph
	 * @param CFG
	 * @return VFG
	 */
	ValueFlowGraph<T> valueFlowAnalysis(IRControlFlowGraph CFG);

	/**
	 * Initialize partition checker
	 */
	void initChecker();
}
