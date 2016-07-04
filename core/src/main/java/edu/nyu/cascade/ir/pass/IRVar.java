package edu.nyu.cascade.ir.pass;

import xtc.type.Type;

/**
 * A class which maintains information about an expression (variable or access
 * path) that may be involved in an alias.
 * 
 * @author Wei
 *
 */

public interface IRVar {
	String getName();

	Type getType();

	String getScopeName();

	void setProperty(String id, Object o);

	Object getProperty(String id);
}
