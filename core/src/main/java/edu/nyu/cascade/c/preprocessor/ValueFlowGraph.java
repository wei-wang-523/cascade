package edu.nyu.cascade.c.preprocessor;

import java.util.Collection;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;

import xtc.tree.Printer;
import edu.nyu.cascade.ir.IRStatement;

public class ValueFlowGraph<T> {

	private final String name;
	private final Set<T> nodes;
	private final Set<ValueFlowEdge<T>> edges;
	private final Multimap<T, ValueFlowEdge<T>> incoming, outgoing;
	
	public ValueFlowGraph(String name) {
		this.name = name;
		nodes = Sets.newHashSet();
		edges = Sets.newHashSet();
		incoming = HashMultimap.create();
		outgoing = HashMultimap.create();
	}
	
	Set<T> getNodes() {
		return nodes;
	}
	
	Collection<ValueFlowEdge<T>> getEdges() {
		return edges;
	}
	
	Collection<ValueFlowEdge<T>> getIncomingEdges(T node) {
		return incoming.get(node);
	}
	
	Collection<ValueFlowEdge<T>> getOutgoingEdges(T node) {
		return outgoing.get(node);
	}
	
	public boolean addEdge(T source, IRStatement stmt, T target) {
		return addEdge(ValueFlowEdge.createEdge(source, target, stmt));
	}
	
	private boolean addEdge(ValueFlowEdge<T> edge) {
		Preconditions.checkNotNull(edge.getSource());
		Preconditions.checkNotNull(edge.getTarget());
	  T source = edge.getSource();
	  T target = edge.getTarget();
	
	  addNode(source);
	  addNode(target);
	  /*
	   * addOutgoingEdge(source, edge); addIncomingEdge(target, edge);
	   */
	  boolean fresh = edges.add(edge);
	  if(fresh) { // new edge
	  	outgoing.put(source, edge);
	  	incoming.put(target, edge);
	  }
	  
	  return fresh;
	}
	
	boolean addNode(T node) {
		return nodes.add(node);
	}
	
	void removeEdge(ValueFlowEdge<T> edge) {
		outgoing.remove(edge.getSource(), edge);
		incoming.remove(edge.getTarget(), edge);
		edges.remove(edge);
	}
	
	public void format(Printer printer) {
	  printer
    	.p("ValueFlowGraph for: " + name)
    	.incr();

	  for (T node : getNodes()) {
	  	printer.pln();
	  	formatNode(printer, node);
	  }
	  printer.decr().pln();
	}
	
  private void formatNode(Printer printer, T node) {
    printer.p(node.toString()).incr().pln();
    for (ValueFlowEdge<T> edge : getOutgoingEdges(node)) {
      printer.indent().pln(edge.toString());
    }
    printer.decr();
  }
}
