package edu.nyu.cascade.c.preprocessor;

import java.util.Set;

import com.google.common.collect.ImmutableMap;

import xtc.type.Type;

/**
 * A class for computing aliases among variables.
 * @author Wei
 *
 */
public interface IRPreAnalysis {
  
  /**
   * Add a variable with @param name, @param type and @param Scope 
   * into the the analyzer.
   * @return an alias variable
   */
  
  IREquivalentVar addVariable(String name, String scope, Type type) ;
  
  /**
   * Compute aliases for the assignment of an address (x = &y).
   * @param lhs
   * @param addr
   */
  void addrAssign(IREquivalentVar lhs, IREquivalentVar addr);
  
  /**
   * Compute aliases for assigning to a pointer (*x = y).
   * @param ptr
   * @param rhs
   */
  void assignPtr(IREquivalentVar ptr, IREquivalentVar rhs);
  
  /**
   * Compute aliases for assigning dynamically allocated memory.
   * @param lhs
   */
  void heapAssign(IREquivalentVar lhs, Type lhsType);
  
  /**
   * Compute alias for an operation (x = op(y1,�,yN)).
   * @param lhs
   * @param opnds
   */
  void opAssign(IREquivalentVar lhs, Iterable<IREquivalentVar> opnds);
  
  /**
   * Compute aliases for a pointer assignment (x = *y).
   * @param lhs
   * @param ptr
   */
  void ptrAssign(IREquivalentVar lhs, IREquivalentVar ptr);
  
  /**
   * Compute aliases for assignment statement (x = y).
   * @param lhs
   * @param rhs
   */
  void simpleAssign(IREquivalentVar lhs, IREquivalentVar rhs);
  
  /**
   * Compute aliases caused by a function call.
   * @param lhs
   * @param func
   * @param args
   */
  void functionCall(IREquivalentVar lhs, IREquivalentVar func, Iterable<IREquivalentVar> args) ;
  
  /**
   * Compute aliases for the formal parameters and return value of a function definition.
   * @param func
   * @param params
   * @param retval
   */
  void functionDef(IREquivalentVar func, Iterable<IREquivalentVar> params, IREquivalentVar retval) ;
  
  /**
   * Get the representative type variable
   */
  
  IREquivalentVar getRepVar(String name, String scope, Type type) ;
  
  /**
   * Get the snapshot map of analysis
   */
  ImmutableMap<IREquivalentVar, Set<IREquivalentVar>> snapshot() ;
  
  /**
   * Get the region var allocated for <code>var</code>
   * @param var
   */
  IREquivalentVar getAllocRegion(IREquivalentVar var);
  
  /**
   * Get the representative of points to var of @param var
   */
  IREquivalentVar getPointsToRepVar(IREquivalentVar var);
  
  /**
   * Get the snapshot of the alias partition sets
   */
  String displaySnapShort();
  
  /**
   * Get the null location
   */
  IREquivalentVar getNullLoc();

  /**
   * Get all alias vars in the same partition of @param var
   */
  IREquivalentClosure getEquivClass(IREquivalentVar var);

}
