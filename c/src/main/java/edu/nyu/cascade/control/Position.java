package edu.nyu.cascade.control;

import java.io.File;
import java.math.BigInteger;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import edu.nyu.cascade.control.jaxb.InsertionType;
import edu.nyu.cascade.control.jaxb.Position.Command;
import edu.nyu.cascade.ir.AbstractLocation;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRLocations;

public class Position extends AbstractLocation implements IRLocation  {
//  public static enum Insert { BEFORE, AFTER };

/*  static edu.nyu.cascade.control.Position valueOf(
      edu.nyu.cascade.control.jaxb.Position position,
      Map<BigInteger, File> sourceFiles)
      throws ControlFileException {
   return valueOf(position,sourceFiles,InsertionType.BEFORE);
  }
  
*/
  static edu.nyu.cascade.control.Position valueOf(
      edu.nyu.cascade.control.jaxb.Position position,
      Map<BigInteger, File> sourceFiles)
      throws ControlFileException {
    // System.out.println(position.getFileId() + ":" + position.getLineNum());
    File file = sourceFiles.get(position.getFileId());
    if (file == null) {
      throw new ControlFileException("Invalid position: " + position);
    }
    
    List<CallPoint> functions = Lists.newArrayList();   
    for(edu.nyu.cascade.control.jaxb.CallPoint pos : position.getFunction())
      functions.add(CallPoint.valueOf(pos, position, sourceFiles));
    
    List<LoopPoint> loops = Lists.newArrayList();   
    for(edu.nyu.cascade.control.jaxb.LoopPoint pos : position.getLoop())
      loops.add(LoopPoint.valueOf(pos, position, sourceFiles));
    
    return new Position(position.getCommand(), file, position.getLine(), position.getInsert(),
        functions, loops);
  }

  private final List<Command> commands;
  private final File file;
  private final BigInteger line;
  private final InsertionType insertionType;
  private final List<CallPoint> functions; 
  private final List<LoopPoint> loops;
  private String invariant = null;
  // Since the above fields are immutable we lazily build a
  // string representation for toString on demand, then cache it
  private String asString;

  public Position(List<Command> commands, File file, BigInteger line, InsertionType insertionType,
      List<CallPoint> functions, List<LoopPoint> loops) {
    Preconditions.checkNotNull(file);
    Preconditions.checkNotNull(line);
    
    this.commands = commands;
    this.file = file;
    this.line = line;
    this.insertionType = insertionType;
    this.functions = functions;
    this.loops = loops;
    
    /* Build stringrep */
    StringBuilder builder = new StringBuilder();
    builder.append( InsertionType.BEFORE.equals(insertionType) ? "^" : "_");
    IRLocations.buildStringOf(this,builder);
    for(Command command : commands) {
      builder.append('@').append(command.getCascadeFunction().trim()).append(
      '(');
      for(String arg : command.getArgument())
        builder.append(arg.trim()).append(',');
      builder.replace(builder.length()-1, builder.length(), ")");
    }
    this.asString = builder.toString();
  }

  public List<Command> getCommands() {
    return Collections.unmodifiableList(commands);
  }

  public File getFile() {
    return file;
  }

  public int getLine() {
    return line.intValue();
  }

  public String toString() {
    return asString;
  }

  public InsertionType getInsertionType() {
    return insertionType;
  }
  
  public List<CallPoint> getFunctions() {
    return Collections.unmodifiableList(functions);
  }
  
  public List<LoopPoint> getLoops() {
    return Collections.unmodifiableList(loops);
  }
  
  public Boolean hasFunctions() {
    return (!functions.isEmpty());
  }
  
  public Boolean hasLoop() {
    return (!loops.isEmpty());
  }
  
  public boolean hasInvariant() {
  	return invariant != null;
  }

  public String getInvariant() {
    return invariant;
  }

  public void setInvariant(String invariant) {
    this.invariant = invariant;
  }
}
