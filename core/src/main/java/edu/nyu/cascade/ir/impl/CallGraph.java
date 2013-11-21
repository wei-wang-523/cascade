package edu.nyu.cascade.ir.impl;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

import xtc.tree.Node;
import xtc.tree.Printer;

import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRCallGraphNode;
import edu.nyu.cascade.ir.IRCallGraph;

public class CallGraph implements IRCallGraph {
  private final Set<CallGraphNode> nodes;
  private final Map<CallGraphNode, Set<CallEdge>> incoming, outgoing;

  private CallGraph() {
    nodes = Sets.newHashSet();
    incoming = Maps.newHashMap();
    outgoing = Maps.newHashMap();
  }
  
  public static CallGraph create() {
  	return new CallGraph();
  }

  public void addCallEdge(CallGraphNode source, Node call,
      CallGraphNode target) {
    addCallEdge(CallEdge.create(source, call, target));
  }

  private void addCallEdge(CallEdge CallEdge) {
    CallGraphNode source = CallEdge.getSource();
    CallGraphNode target = CallEdge.getTarget();

    addNode(source);
    addNode(target);
    /*
     * addOutgoingCallEdge(source, CallEdge); addIncomingCallEdge(target, CallEdge);
     */
    addCallEdgeToMap(outgoing, source, CallEdge);
    addCallEdgeToMap(incoming, target, CallEdge);
  }

  private void addCallEdgeToMap(Map<CallGraphNode, Set<CallEdge>> map,
      IRCallGraphNode source, CallEdge CallEdge) {
    // node should already exist
    assert (nodes.contains(source));
    Set<CallEdge> CallEdges = map.get(source);
    // CallEdges should be initialized in addNode
    assert (CallEdges != null);
    CallEdges.add(CallEdge);
  }

  private boolean addNode(CallGraphNode source) {
    if (nodes.contains(source)) {
      return false;
    }
    nodes.add(source);
    incoming.put(source, Sets.<CallEdge> newHashSet());
    outgoing.put(source, Sets.<CallEdge> newHashSet());
    return true;
  }
  
  public void format(Printer printer) {
    printer
        .p("Call graph: ")
        .incr();

    for (CallGraphNode node : getNodes()) {
      printer.pln();
      formatNode(printer, node);
    }
    printer.decr();
  }

  private void formatNode(Printer printer, CallGraphNode node) {
    node.format(printer);
    printer.incr();
    for (CallEdge CallEdge : getOutgoingEdges(node)) {
      printer.indent().pln(CallEdge.toString());
    }
    printer.decr();
  }
  
  @Override
  public Set<CallGraphNode> getNodes() {
    return Collections.<CallGraphNode> unmodifiableSet(nodes);
  }

  @Override
  public Set<CallEdge> getIncomingEdges(IRCallGraphNode node) {
    assert (incoming.get(node) != null);
    return Collections.unmodifiableSet(incoming.get(node));
  }

  @Override
  public Set<CallEdge> getOutgoingEdges(IRCallGraphNode node) {
    assert (outgoing.get(node) != null);
    return Collections.unmodifiableSet(outgoing.get(node));
  }
  
  @Override
  public IRCallGraphNode getCallee(IRCallGraphNode funcNode, final Node node) {
  	assert (outgoing.get(funcNode) != null);
  	Iterable<CallEdge> outgoingEdges = outgoing.get(funcNode);
  	return Iterables.find(outgoingEdges, new Predicate<CallEdge>(){
			@Override
			public boolean apply(CallEdge edge) {
				return edge.getCallNode().equals(node);
			}  		
  	}).getTarget();
  }
  
  @Override
  public IRCallGraphNode getCaller(IRCallGraphNode funcNode, final Node node) {
  	assert (incoming.get(funcNode) != null);
  	Iterable<CallEdge> incomingEdges = incoming.get(funcNode);
  	return Iterables.find(incomingEdges, new Predicate<CallEdge>(){
			@Override
			public boolean apply(CallEdge edge) {
				return edge.getCallNode().equals(node);
			}  		
  	}).getSource();
  }
  
  @Override
  public boolean hasCaller(IRCallGraphNode funcNode, final Node node) {
  	assert (incoming.get(funcNode) != null);
  	Iterable<CallEdge> incomingEdges = incoming.get(funcNode);
  	return Iterables.any(incomingEdges, new Predicate<CallEdge>(){
			@Override
			public boolean apply(CallEdge edge) {
				return edge.getCallNode().equals(node);
			}  		
  	});
  }
  
  @Override
  public boolean hasCallee(IRCallGraphNode funcNode, final Node node) {
  	assert (outgoing.get(funcNode) != null);
  	Iterable<CallEdge> outgoingEdges = outgoing.get(funcNode);
  	return Iterables.any(outgoingEdges, new Predicate<CallEdge>(){
			@Override
			public boolean apply(CallEdge edge) {
				return edge.getCallNode().equals(node);
			}  		
  	});
  }

  @Override
  public Set<CallGraphNode> getPredecessors(IRCallGraphNode node) {
    return CallEdge.getSources(getIncomingEdges(node));
  }

  @Override
  public Set<CallGraphNode> getSuccessors(IRCallGraphNode node) {
    return CallEdge.getTargets(getOutgoingEdges(node));
  }
}
