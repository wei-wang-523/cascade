package edu.nyu.cascade.c.preprocessor;

import xtc.type.Type;

/**
 * A class which maintains information about an expression (variable 
 * or access path) that may be involved in an alias.
 * 
 * @author Wei
 *
 */

public interface IRVar {
  String getName() ;
  Type getType() ;
  String getScope() ;
  boolean isNullLoc() ;
  String toString() ;
}
