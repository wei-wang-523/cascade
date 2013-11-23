package edu.nyu.cascade.ir.impl;

import java.util.Collections;
import java.util.Set;

import xtc.tree.Node;
import xtc.tree.Printer;

import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRCallEdge;

public class CallEdge implements IRCallEdge<CallGraphNode> {
	
  static CallEdge create(CallGraphNode currentNode, Node call, CallGraphNode succ) {
    return new CallEdge(currentNode, call, succ);
  }

  private final CallGraphNode source, target;
  private final Node call;

  private CallEdge(CallGraphNode currentNode, Node call, CallGraphNode succ) {
    this.source = currentNode;
    this.target = succ;
    this.call = call;
  }

  @Override
  public boolean equals(Object o) {
    if (!(o instanceof CallEdge)) {
      return false;
    }
    CallEdge edge = (CallEdge) o;
    return (edge != null && source.equals(edge.source)
            && target.equals(edge.target) && (call == edge.call));
  }

  @Override
  public CallGraphNode getSource() {
    return source;
  }

  @Override
  public CallGraphNode getTarget() {
    return target;
  }

  @Override
  public int hashCode() {
    int sourceHash = source.hashCode();
    int edgeHash = call==null ? 0 : call.hashCode();
    int targetHash = target.hashCode();
    
    return sourceHash ^ edgeHash ^ targetHash;
  }
  
  @Override
  public void format(Printer printer) {
    printer.pln(toString());
  }
  
  @Override
  public String toString() {
    return getSource().getName() + " --" + (call == null ? "" : "[" + call.getLocation() + "]") +
        "--> " + getTarget().getName();
  }

  public static Set<CallGraphNode> getSources(Iterable<CallEdge> edges) {
    Set<CallGraphNode> preds = Sets.newHashSet();
    for (CallEdge edge : edges) {
      preds.add(edge.getSource());
    }
    return Collections.unmodifiableSet(preds);
  }
  
  public static Set<CallGraphNode> getTargets(Iterable<CallEdge> edges) {
    Set<CallGraphNode> preds = Sets.newHashSet();
    for (CallEdge edge : edges) {
      preds.add(edge.getTarget());
    }
    return Collections.unmodifiableSet(preds);
  }

	@Override
  public Node getCallNode() {
	  return call;
  }
}
