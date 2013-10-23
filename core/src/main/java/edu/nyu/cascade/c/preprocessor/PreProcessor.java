package edu.nyu.cascade.c.preprocessor;

import java.util.Set;

import xtc.tree.Node;

import com.google.common.collect.ImmutableMap;

import edu.nyu.cascade.ir.IRStatement;

/**
 * Pre-analysis statement
 * @author Wei
 *
 */
public interface PreProcessor<T> {

  /**
   * Pre analysis statement <code>stmt</code>
   * @param stmt
   */
	void analysis(IRStatement stmt);

  /**
   * Display the snap shot
   */
	String displaySnapShot();

	IREquivClosure getEquivClass(T arg);

	ImmutableMap<T, Set<IRVar>> snapshot();

	T getPointsToElem(Node node);

	IRVar getAllocateElem(Node node);

	String getRepName(T arg);

	T getRep(Node node);
}
