package edu.nyu.cascade.ir.impl;

import java.util.Set;

import xtc.tree.Node;
import xtc.tree.Printer;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRCallGraphNode;
import edu.nyu.cascade.ir.IRVarInfo;

public class CallGraphNode implements IRCallGraphNode {

  public static CallGraphNode create(IRVarInfo info) {
    return new CallGraphNode(info);
  }
  
  private final IRVarInfo info;
  private final Set<IRCallGraphNode> calledFunctions;
  
  private CallGraphNode(IRVarInfo info) {
  	this.info = info;
  	this.calledFunctions = Sets.newHashSet();
  }

  @Override
  public String toString() {
    return info.toString();
  }

  void format(Printer printer) {
    printer
        .pln("CallGraphNode " + toString());
  }

	@Override
  public void addCalledFunction(IRCallGraphNode function) {
		calledFunctions.add(function);
  }

	@Override
  public ImmutableSet<IRCallGraphNode> getCalledFunctions() {
	  return ImmutableSet.copyOf(calledFunctions);
  }

	@Override
  public Node getFuncDeclareNode() {
	  return info.getDeclarationNode();
  }

	@Override
  public String getName() {
	  return info.getName();
  }

	@Override
  public IRVarInfo getFunctionInfo() {
	  return info;
  }

}
