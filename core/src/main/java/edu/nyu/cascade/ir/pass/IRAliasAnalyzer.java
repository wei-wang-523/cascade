package edu.nyu.cascade.ir.pass;

import java.util.Collection;
import java.util.Map;

import xtc.tree.Node;

import com.google.common.collect.Range;

import edu.nyu.cascade.prover.Expression;

/**
 * Pre-analysis statement
 * @author Wei
 *
 */
public interface IRAliasAnalyzer<T> extends IRPass {	
  /**
   * Display the snap shot
   */
	String displaySnapShot();

	void buildSnapShot();

	T getPointsToLoc(T rep);
	
	long getRepTypeWidth(T rep);

	String getRepId(T rep);

	T getRep(Node node);
	
	T getStackRep(Node node);
	
	/**
	 * Get the field representative of <code>rep</code>. It's
	 * used to in field-sensitive steensgaard analysis, to find 
	 * the elements' representative for the structure components
	 * 
	 * @param rep
	 * @return
	 */
	Collection<T> getFillInReps(T rep, long length);

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
	Map<Range<Long>, T> getStructMap(T rep,  long length);

	Collection<IRVar> getEquivFuncVars(Node funcNode);

	boolean isAccessTypeSafe(T rep);
}
