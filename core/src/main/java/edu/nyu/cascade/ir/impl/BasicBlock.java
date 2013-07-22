package edu.nyu.cascade.ir.impl;

import java.math.BigInteger;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import xtc.tree.Location;
import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRLocations;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.util.Preferences;

public class BasicBlock implements IRBasicBlock, Comparable<BasicBlock> {
  private static BigInteger nextId = BigInteger.ZERO;

  public static BasicBlock create() {
    return new BasicBlock();
  }

  public static BasicBlock loopBlock(Location loc) {
    return new BasicBlock(Type.LOOP, loc);
  }

  public static BasicBlock entryBlock(Location loc) {
    return new BasicBlock(Type.ENTRY, loc);
  }
  
  public static BasicBlock exitBlock() {
    return new BasicBlock(Type.EXIT);
  }

  public static BasicBlock switchBlock(Location loc) {
    return new BasicBlock(Type.SWITCH, loc);
  }
  
  public static BasicBlock mergeBlock(IRBasicBlock switchBlock) {
    return new BasicBlock(Type.MERGE, switchBlock);
  }
  
  private final BigInteger id;
  private final Type type;
  private List<IRStatement> statements;
  private IRLocation startLocation, endLocation;
  private final Set<String> preLabels, postLabels;
  private int iterTimes;
  private Scope scope;
  private IRBasicBlock swichBlock;
  
  private BasicBlock() {
    this(Type.BLOCK);
  }

  private BasicBlock(Type type) {
    this(type,Collections.<IRStatement> emptyList());
    this.startLocation = null;
    this.endLocation = null;
  }

  private BasicBlock(Type type, Location loc) {
    this(type, Collections.<IRStatement> emptyList());
    this.startLocation = IRLocations.ofLocation(loc);
    this.endLocation = IRLocations.ofLocation(loc);
  }

  private BasicBlock(Type type, IRBasicBlock switchBlock) {
    this(type, Collections.<IRStatement> emptyList());
    Preconditions.checkArgument(switchBlock.getType().equals(IRBasicBlock.Type.SWITCH));
    this.swichBlock = switchBlock;
  }
  
  private BasicBlock(Type type, List<IRStatement> statements) {
    this.id = nextId;
    this.type = type;
    this.statements = Lists.newArrayListWithCapacity(statements.size());
    this.preLabels = Sets.newHashSet();
    this.postLabels = Sets.newHashSet();
    nextId = nextId.add(BigInteger.ONE);
    if(type.equals(IRBasicBlock.Type.LOOP)) {
      if(Preferences.isSet(Preferences.OPTION_ITERATION_TIMES))
        this.iterTimes = Preferences.getInt(Preferences.OPTION_ITERATION_TIMES);
      else
        this.iterTimes = 0;
    } else {
      this.iterTimes = 0;
    }
    
    addStatements(statements);
  }

  private void updateLocations() {
    if (!statements.isEmpty()) {
      startLocation = statements.get(0).getLocation();
      endLocation = statements
          .get(statements.size() - 1)
          .getLocation();
    }
  }
  
  public void addPreLabel(String label) { 
    preLabels.add(label);
  }
  
  public void addPostLabel(String label) { 
    postLabels.add(label);
  }
  
  public void addStatement(IRStatement statement) {
    statements.add(statement);
    addLocation(statement.getLocation());
  }

  public void addStatements(List<? extends IRStatement> statements) {
    if( !statements.isEmpty() ) {
      this.statements.addAll(statements);
//      addLocation( statements.get(statements.size()-1).getLocation());
      addLocation(statements.get(0).getLocation(), statements.get(statements.size()-1).getLocation());
    }
  }
  
  public void addStatement(int index, IRStatement statement) {
    statements.add(index, statement);
    addLocation(statement.getLocation());
  }

  public void addStatements(int index, List<? extends IRStatement> statements) {
    if( !statements.isEmpty() ) {
      this.statements.addAll(index, statements);
//      addLocation( statements.get(statements.size()-1).getLocation());
      addLocation(statements.get(0).getLocation(), statements.get(statements.size()-1).getLocation());
    }
  }

  @Override
  public BigInteger getId() {
    return id;
  }  
  
  @Override
  public void setScope(Scope scope) {
    this.scope = scope;
  }

  @Override
  public Scope getScope() {
    return this.scope;
  }
  
  @Override
  public int getIterTimes() {
    return iterTimes;
  }
  
  @Override
  public void setIterTimes(int iterTimes) {
    this.iterTimes = iterTimes;
  }
  
  @Override
  public void clearIterTimes() {
    this.iterTimes = 0;
  }

  @Override
  public Type getType() {
    return type;
  }

  @Override
  public ImmutableList<IRStatement> getStatements() {
    return ImmutableList.copyOf(statements);
  }

  @Override
  public BasicBlock splitBefore(IRLocation position) {
    int i = 0;
    for (IRStatement stmt : statements) {
      if (position.precedes(stmt)) {
        break;
      }
      i++;
    }
    List<IRStatement> nextStmts = statements.subList(i, statements.size());
    BasicBlock next = new BasicBlock(type, nextStmts);
    next.setScope(getScope());
    nextStmts.clear(); // removes the sublist from this.statements
    updateLocations();
    return next;
  }
  
  @Override
  public BasicBlock splitAfter(IRLocation position) {
    int i = 0;
    for (IRStatement stmt : statements) {
      if (position.strictPrecedes(stmt)) {
        break;
      }
      i++;
    }
    List<IRStatement> nextStmts = statements.subList(i, statements.size());
    BasicBlock next = new BasicBlock(type, nextStmts);
    next.setScope(getScope());
    nextStmts.clear(); // removes the sublist from this.statements
    updateLocations();
    return next;
  }
  
  @Override
  public ImmutableSet<String> getPreLabels() {
    return ImmutableSet.copyOf(preLabels);
  }
  
  @Override
  public ImmutableSet<String> getPostLabels() {
    return ImmutableSet.copyOf(postLabels);
  }
  
  @Override
  public IRLocation getStartLocation() {
    return startLocation;

  }

  @Override
  public IRLocation getEndLocation() {
    return endLocation;
  }

  @Override
  public String toString() {
    String s = getId() + ":" + type;
    
    if( getStartLocation() != null ) {
      s += "@" + getStartLocation() ;
    }

    return s;
  }

  @Override
  public Node getStartNode() {
    IRStatement stmt = getFirstStatement();
    return stmt == null ? null : stmt.getSourceNode();
  }

  private IRStatement getFirstStatement() {
    if (statements.isEmpty()) {
      return null;
    } else {
      return statements.get(0);
    }
  }

  void format(Printer printer) {
    printer
        .pln("Block " + toString() + " " + preLabels.toString())
        .incr();
    for (IRStatement statement : getStatements()) {
      printer.indent();
      if( !statement.getPreLabels().isEmpty() ) {
        printer.p(statement.getPreLabels() + " ");
      }
      printer.p(statement.toString());
      if( !statement.getPostLabels().isEmpty() ) {
        printer.p(" " + statement.getPostLabels());
      }
      printer.pln();
    }
    printer.indent().pln(postLabels.toString());
    printer.decr();
  }

  @Override
  public int compareTo(BasicBlock b) {
    return getId().compareTo(b.getId());
  }

  @Override
  public boolean hasLocation() {
    assert( (getStartLocation() == null) == (getEndLocation() == null) );
    return getStartLocation() != null;
  }
  
  @Override
  public void addLocation(IRLocation loc) {
    if( startLocation == null || loc.precedes(startLocation) ) {
      startLocation = loc;
    } 
    if( endLocation == null || loc.follows( endLocation ) ) {
      endLocation = loc;
    }
  }
  
  public void addLocation(IRLocation startLoc, IRLocation endLoc) {
    if( startLocation == null || startLoc.precedes(startLocation) ) {
      startLocation = startLoc;
    } 
    if( endLocation == null || endLoc.follows( endLocation ) ) {
      endLocation = endLoc;
    }
  }

  public boolean isEmpty() {
    return type == Type.BLOCK && getStatements().isEmpty();
  }

  public void addPreLabels(Iterable<String> preLabels) {
    Iterables.addAll(this.preLabels,preLabels);
  }
  
  public void addPostLabels(Iterable<String> postLabels) {
    Iterables.addAll(this.postLabels,postLabels);
  }
  
  public IRBasicBlock getSwitchBlock() {
    Preconditions.checkArgument(type.equals(IRBasicBlock.Type.MERGE));
    return this.swichBlock;
  }

}
