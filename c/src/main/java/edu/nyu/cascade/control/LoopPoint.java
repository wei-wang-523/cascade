package edu.nyu.cascade.control;

import java.io.File;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;

import com.google.inject.internal.Lists;
import com.google.inject.internal.Preconditions;

public class LoopPoint {

  static edu.nyu.cascade.control.LoopPoint valueOf(
      edu.nyu.cascade.control.jaxb.LoopPoint loopPos,
      Map<BigInteger, File> sourceFiles)
      throws ControlFileException {
    if(loopPos == null)
      return null;
    BigInteger iterTimes = loopPos.getIterTimes();
    String invariant = loopPos.getInvariant();
    List<Position> wayPoint = Lists.newArrayList();   
    for(edu.nyu.cascade.control.jaxb.Position pos : loopPos.getWayPoint())
      wayPoint.add(Position.valueOf(pos, sourceFiles));
    return new LoopPoint(iterTimes, invariant, wayPoint);
  }

  private int iterTimes;
  private String invariant;
  private final List<Position> wayPoint; 
  private String asString;

  private LoopPoint(BigInteger iterTimes, String invariant, List<Position> wayPoint) {
    // Cannot be: iterTimes > 0 and invariant is not null
    Preconditions.checkArgument(!(iterTimes.intValue() > 0 && invariant != null));
    this.iterTimes = iterTimes.intValue();
    this.wayPoint = wayPoint;
    this.invariant = invariant;
    
    /* Build stringrep */
    StringBuilder builder = new StringBuilder();
    builder.append("loop:" + iterTimes);
    builder.append("invariant:" + invariant);
    this.asString = builder.toString();
  }

  public String toString() {
    return asString;
  }
  
  public int getIterTimes() {
    return iterTimes;
  }
  
  public String getInvariant() {
    return invariant;
  }
  
  public List<Position> getWayPoint() {
    return wayPoint;
  }
}
