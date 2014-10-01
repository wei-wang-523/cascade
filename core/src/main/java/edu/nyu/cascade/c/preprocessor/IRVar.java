package edu.nyu.cascade.c.preprocessor;

import edu.nyu.cascade.prover.Expression;
import xtc.type.Type;
/**
 * A class which maintains information about an expression (variable 
 * or access path) that may be involved in an alias.
 * 
 * @author Wei
 *
 */

public interface IRVar {
	String toStringShort();
  String getName() ;
  Type getType() ;
  String getScopeName();
	Expression getExpr();
	
	/** Check whether it has a heap tag or not */
	boolean hasHeapTag();
	
	void setProperty(String id, Object o);
	Object getProperty(String id);
}
