package edu.nyu.cascade.ir.pass;

import java.util.Collection;
import java.util.Map;

import xtc.tree.Node;
import xtc.type.Type;

import com.google.common.collect.Range;

import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.Pair;

/**
 * Pre-analysis statement
 * 
 * @author Wei
 *
 */
public interface IRAliasAnalyzer<T> extends IRPass {
	/**
	 * Display the snap shot
	 */
	String displaySnapShot();

	void buildSnapShot();

	T getPtsToRep(Node node);

	T getPtsToFieldRep(T rep);

	long getRepWidth(T rep);

	String getRepId(T rep);

	T getRep(Node node);

	T getStackRep(Node node);

	/**
	 * Get the field representatives within rep. It is used to in field-sensitive
	 * points-to analysis, to find the elements' representative for the innder
	 * components
	 * 
	 * @param rep
	 * @return
	 */
	Collection<T> getFieldReps(T rep, Type Ty);

	/**
	 * Add an newly allocated <code>region</code> with source node
	 * <code>ptrNode</code>
	 * 
	 * @param region
	 * @param ptrNode
	 * @return
	 */
	void addRegion(Expression region, Node ptrNode);

	/**
	 * Add a stack variable with expression <code>lval</code>, with source node
	 * <code>lvalNode</code>
	 * 
	 * @param lval
	 * @param lvalNode
	 */
	void addVar(Expression lval, Node lvalNode);

	/**
	 * Get the mapping from offset to ECR in structure ECR only used for
	 * field-sensitive analysis
	 * 
	 * @param rep
	 * @return
	 */
	Map<Range<Long>, T> getStructMap(T rep, long length);

	Collection<IRVar> getEquivFuncVars(Node funcNode);

	void analyzeVarArg(String func, Type funcTy, Node varArgN);

	Pair<Integer, Integer> getAliasAnalysisStats(IRControlFlowGraph globalCFG,
			Collection<IRControlFlowGraph> CFGs);
}
