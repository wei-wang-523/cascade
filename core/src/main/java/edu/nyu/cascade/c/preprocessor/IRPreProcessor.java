package edu.nyu.cascade.c.preprocessor;

import edu.nyu.cascade.ir.IRStatement;

/**
 * Pre-analysis statement
 * @author Wei
 *
 */
public interface IRPreProcessor {

  /**
   * Pre analysis statement <code>stmt</code>
   * @param stmt
   */
	void analysis(IRStatement stmt);

  /**
   * Display the snap shot
   */
	String displaySnapShot();
}
