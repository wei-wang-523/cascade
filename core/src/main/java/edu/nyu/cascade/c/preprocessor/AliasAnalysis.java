package edu.nyu.cascade.c.preprocessor;

import java.util.Set;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;

import xtc.type.Type;

/**
 * A class for computing aliases among variables.
 * @author Wei
 *
 */
public interface AliasAnalysis {
  
  /**
   * Add a variable with @param name, @param type and @param Scope 
   * into the the analyzer.
   * @return an alias variable
   */
  
  AliasVar addVariable(String name, String scope, Type type) ;
  
  /**
   * Compute aliases for the assignment of an address (x = &y).
   * @param lhs
   * @param addr
   */
  void addrAssign(AliasVar lhs, AliasVar addr);
  
  /**
   * Compute aliases for assigning to a pointer (*x = y).
   * @param ptr
   * @param rhs
   */
  void assignPtr(AliasVar ptr, AliasVar rhs);
  
  /**
   * Compute aliases for assigning dynamically allocated memory.
   * @param lhs
   */
  void heapAssign(AliasVar lhs, Type lhsType);
  
  /**
   * Compute alias for an operation (x = op(y1,�,yN)).
   * @param lhs
   * @param opnds
   */
  void opAssign(AliasVar lhs, Iterable<AliasVar> opnds);
  
  /**
   * Compute aliases for a pointer assignment (x = *y).
   * @param lhs
   * @param ptr
   */
  void ptrAssign(AliasVar lhs, AliasVar ptr);
  
  /**
   * Compute aliases for assignment statement (x = y).
   * @param lhs
   * @param rhs
   */
  void simpleAssign(AliasVar lhs, AliasVar rhs);
  
  /**
   * Compute aliases caused by a function call.
   * @param lhs
   * @param func
   * @param args
   */
  void functionCall(AliasVar lhs, AliasVar func, Iterable<AliasVar> args) ;
  
  /**
   * Compute aliases for the formal parameters and return value of a function definition.
   * @param func
   * @param params
   * @param retval
   */
  void functionDef(AliasVar func, Iterable<AliasVar> params, AliasVar retval) ;
  
  /**
   * Get the representative type variable
   */
  
  AliasVar getRepVar(String name, String scope, Type type) ;
  
  /**
   * Get the snapshot map of analysis
   */
  ImmutableMap<AliasVar, Set<AliasVar>> snapshot() ;
  
  /**
   * Get the region var allocated for @param var
   */
  AliasVar getAllocRegion(AliasVar var);
  
  /**
   * Get the representative of points to var of @param var
   */
  AliasVar getPointsToRepVar(AliasVar var);
  
  /**
   * Get the snapshot of the alias partition sets
   */
  String displaySnapShort();
  
  /**
   * Get the null location
   */
  AliasVar getNullLoc();

  /**
   * Get all alias vars in the same partition of @param var
   */
  ImmutableSet<AliasVar> getEquivClass(AliasVar var);

}
