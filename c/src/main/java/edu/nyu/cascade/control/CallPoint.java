package edu.nyu.cascade.control;

import java.io.File;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;

import com.google.common.collect.Lists;

public class CallPoint {

  static edu.nyu.cascade.control.CallPoint valueOf(
      edu.nyu.cascade.control.jaxb.CallPoint callPos,
      Map<BigInteger, File> sourceFiles)
      throws ControlFileException {
    String funcName = callPos.getFuncName();
    BigInteger funcId = callPos.getFuncId();
    List<Position> wayPoint = Lists.newArrayList();
    for(edu.nyu.cascade.control.jaxb.Position pos : callPos.getWayPoint())
      wayPoint.add(Position.valueOf(pos, sourceFiles));
    return new CallPoint(funcName, funcId, wayPoint);
  }

  private final String funcName;
  private final BigInteger funcId;
  private final List<Position> wayPoint; 
  private String asString;

  private CallPoint(String funcName, BigInteger funcId, List<Position> wayPoint) {
    this.funcName = funcName;
    this.funcId = funcId;
    this.wayPoint = wayPoint;
    
    /* Build stringrep */
    StringBuilder builder = new StringBuilder();
    builder.append(funcName + "_");
    builder.append(funcId);
    this.asString = builder.toString();
  }

  public String toString() {
    return asString;
  }
  
  public String getFuncName() {
    return funcName;
  }
  
  public BigInteger getFuncId() {
    return funcId;
  }
  
  public List<Position> getWayPoint() {
    return wayPoint;
  }
}
