package edu.nyu.cascade.control;

import java.io.File;
import java.math.BigInteger;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import com.google.common.collect.Lists;

public class CallPoint {

  static edu.nyu.cascade.control.CallPoint valueOf(
      edu.nyu.cascade.control.jaxb.CallPoint callPos,
      edu.nyu.cascade.control.jaxb.Position position, 
      Map<BigInteger, File> sourceFiles)
      throws ControlFileException {
    String funcName = callPos.getFuncName();
    BigInteger col = callPos.getColumn();
    List<Position> wayPoint = Lists.newArrayList();
    for(edu.nyu.cascade.control.jaxb.Position pos : callPos.getWayPoint())
      wayPoint.add(Position.valueOf(pos, sourceFiles));
    
    Position startPosition = null;
    if(callPos.getStartPosition() != null)
      startPosition = Position.valueOf( callPos.getStartPosition(), sourceFiles );
    Position endPosition = null;
    if(callPos.getEndPosition() != null)
      endPosition = Position.valueOf(callPos.getEndPosition(), sourceFiles);
    File file = sourceFiles.get(position.getFileId());
    BigInteger line = position.getLine();
    return new CallPoint(file, line, funcName, col, startPosition, wayPoint, endPosition);
  }

  private final File file;
  private final BigInteger line;
  private final String funcName;
  private final BigInteger column;
  private final Position startPosition;
  private final Position endPosition;
  private final List<Position> wayPoint; 
  private String asString;

  private CallPoint(File file, BigInteger line, 
  		String funcName, BigInteger column, Position startPosition, 
  		List<Position> wayPoint, Position endPosition) {
  	this.file = file;
  	this.line = line;
    this.funcName = funcName;
    this.column = column;
    this.startPosition = startPosition;
    this.wayPoint = wayPoint;
    this.endPosition = endPosition;
    
    /* Build stringrep */
    StringBuilder builder = new StringBuilder();
    builder.append(funcName + "@Col#");
    builder.append(column);
    this.asString = builder.toString();
  }

  public String toString() {
    return asString;
  }
  
  public File getFile() {
		return file;
	}

	public BigInteger getLine() {
		return line;
	}
  
  public String getFuncName() {
    return funcName;
  }
  
  public boolean hasColumn() {
  	return column != null;
  }
  
  public BigInteger getColumn() {
  	if(hasColumn())
  		return column;
  	else
  		return BigInteger.ZERO;
  }
  
  public List<Position> getWayPoint() {
    return Collections.unmodifiableList(wayPoint);
  }
  
  public Position getEndPosition() {
    return endPosition;
  }
  
  public Position getStartPosition() {
    return startPosition;
  }
}
