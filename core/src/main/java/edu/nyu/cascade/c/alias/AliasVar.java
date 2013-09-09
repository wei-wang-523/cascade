package edu.nyu.cascade.c.alias;

import xtc.type.Type;
import xtc.util.SymbolTable.Scope;

/**
 * A class which maintains information about an expression (variable 
 * or access path) that may be involved in an alias.
 * 
 * @author Wei
 *
 */

public interface AliasVar {
  String getName() ;
  Type getType() ;
  Scope getScope() ;
}
