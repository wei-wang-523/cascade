package edu.nyu.cascade.c.preprocessor;

import xtc.type.Type;
import xtc.util.SymbolTable.Scope;

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
  String toString() ;
  Scope getScope();
}
