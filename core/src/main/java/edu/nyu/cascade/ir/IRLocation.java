package edu.nyu.cascade.ir;

import java.io.File;

public interface IRLocation extends Comparable<IRLocation> {
  boolean equals(IRLocation loc);
  /** Returns true if the location follows the basic block. The return value
   * is undefined if the block and the location are not in the same file, or
   * if the block does not have a defined end location.
   */
  boolean follows(IRBasicBlock block);
  boolean follows(IRExpression expr);
  boolean follows(IRLocation loc);
  boolean follows(IRStatement stmt);
  
  boolean follows(IRBasicBlock block, boolean strict);
  boolean follows(IRExpression expr, boolean strict);
  boolean follows(IRLocation loc, boolean strict);
  boolean follows(IRStatement stmt, boolean strict);

  //  int getColumn();
  File getFile();
  int getLine();

  /**
   * Returns true if the location is within the basic block. The return value is
   * undefined if the block does not have defined start location and end
   * locations.
   */
  boolean isWithin(IRBasicBlock block);
  /** Returns true if the location precedes the basic block. The return value
   * is undefined if the block and the location are not in the same file, or
   * if the block does not have a defined start location.
   */
  boolean precedes(IRBasicBlock block);
  boolean precedes(IRExpression expr);
  boolean precedes(IRLocation loc);
  boolean precedes(IRStatement stmt);
  boolean precedes(IRBasicBlock block, boolean strict);
  boolean precedes(IRExpression expr, boolean strict);
  boolean precedes(IRLocation loc, boolean strict);
  boolean precedes(IRStatement stmt, boolean strict);
  boolean strictFollows(IRBasicBlock block);
  boolean strictFollows(IRExpression expr);
  boolean strictFollows(IRLocation loc);
  boolean strictFollows(IRStatement stmt);
  boolean strictPrecedes(IRBasicBlock block);
  boolean strictPrecedes(IRExpression expr);
  boolean strictPrecedes(IRLocation loc);
  boolean strictPrecedes(IRStatement stmt);
}
