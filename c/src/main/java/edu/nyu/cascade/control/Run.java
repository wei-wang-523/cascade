package edu.nyu.cascade.control;

import java.io.File;
import java.math.BigInteger;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import com.google.common.collect.Lists;


public class Run {
  public static Run valueOf(edu.nyu.cascade.control.jaxb.ControlFile.Run run,
     Map<BigInteger,File> sourceFiles) throws ControlFileException {
    Position startPosition = Position.valueOf( run.getStartPosition(), sourceFiles );
    Position endPosition = Position.valueOf(run.getEndPosition(), sourceFiles);
    List<Position> wayPoints = Lists.newArrayList();
    for( edu.nyu.cascade.control.jaxb.Position position : run.getWayPoint() ) {
      wayPoints.add( Position.valueOf( position, sourceFiles ) );
    }
    return new Run(startPosition,endPosition,wayPoints);
  }

  private final Position startPosition;

  private final Position endPosition;

  private final List<Position> wayPoints;
  
  private Run(Position startPosition, Position endPostition) {
    this(startPosition,endPostition,Collections.<Position>emptyList());
  }
  
  private Run(Position startPosition, Position endPostition, List<Position> wayPoints) {
    super();
    this.startPosition = startPosition;
    this.endPosition = endPostition;
    this.wayPoints = Lists.newArrayList(wayPoints);
  }
  
  public Position getEndPosition() {
    return endPosition;
  }
  
  public Position getStartPosition() {
    return startPosition;
  }

  public List<Position> getWayPoints() {
    return Collections.unmodifiableList(wayPoints);
  }
}
