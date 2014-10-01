package edu.nyu.cascade.c.preprocessor;

import java.util.Collection;

import xtc.tree.Node;
import xtc.type.Type;

import com.google.common.collect.ImmutableMap;

import edu.nyu.cascade.ir.IRStatement;
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

	ImmutableMap<T, Collection<IRVar>> getSnapShot();

	T getPointsToRep(Node node);
	
	Type getRepType(T rep);

	String getRepId(T rep);

	T getRep(Node node);
	
	/**
	 * Get the source representative of <code>rep</code>. It's
	 * used to in field-sensitive steensgaard analysis, to find 
	 * the parent representative for the structure components
	 * 
	 * @param rep
	 * @return
	 */
	T getSrcRep(T rep);

	/**
	 * Pre analysis statement <code>stmt</code>
	 * @param stmt
	 */
	void analysis(IRStatement stmt);

	/**
	 * Add an newly allocated variable with variable information 
	 * <code>info</code> in the partition with representative 
	 * <code>rep</code>
	 * @param rep
	 * @param rep
	 * @return
	 */
	void addAllocRegion(T rep, Expression region);

	/**
	 * Add a stack variable with expression <code>lval</code>
	 * @param lval
	 */
	IRVar addStackVar(Expression lval);
}
