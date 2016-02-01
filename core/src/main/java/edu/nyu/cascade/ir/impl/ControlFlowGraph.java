package edu.nyu.cascade.ir.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;

import xtc.tree.Location;
import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Queues;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRBooleanExpression;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;

public class ControlFlowGraph implements IRControlFlowGraph {
  private final Node sourceNode;
  private final String name;
  private BasicBlock entry, exit;
  private final SortedSet<BasicBlock> nodes;
  private final Multimap<BasicBlock, Edge> incoming, outgoing;
  private final LinkedHashSet<Edge> edges;
  private final Scope scope;

  public ControlFlowGraph(Node sourceNode, String name, Scope scope) {
    this.sourceNode = sourceNode;
    this.name = name;
    this.scope = scope;

    entry = BasicBlock.entryBlock(sourceNode.getLocation());
    entry.setScope(scope);
    exit = BasicBlock.exitBlock();
    exit.setScope(scope);
    nodes = Sets.newTreeSet();
    edges = Sets.newLinkedHashSet();
    nodes.add(entry); nodes.add(exit);
    incoming = LinkedHashMultimap.create();
    outgoing = LinkedHashMultimap.create();
  }
  
  private ControlFlowGraph(Node sourceNode, 
  		String name,
  		Scope scope,
  		SortedSet<BasicBlock> nodes,
  		LinkedHashSet<Edge> edges,
  		BasicBlock entryBlock, 
  		BasicBlock exitBlock,
  		Multimap<BasicBlock, Edge> incoming,
  		Multimap<BasicBlock, Edge> outgoing) {
    this.sourceNode = sourceNode;
    this.name = name;
    this.scope = scope;

    this.entry = entryBlock;
    this.exit = exitBlock;
    this.nodes = nodes;
    this.edges = edges;
    this.incoming = incoming;
    this.outgoing = outgoing;
  }
  
  /**
   * Create a new CFG without any function source node attached
   * @param entryBlock
   * @param exitBlock
   */
  public static ControlFlowGraph create(IRBasicBlock entryBlock, IRBasicBlock exitBlock) {
  	SortedSet<BasicBlock> nodes = Sets.newTreeSet();
  	LinkedHashSet<Edge> edges = Sets.newLinkedHashSet();
  	if(entryBlock != null)	nodes.add((BasicBlock) entryBlock);
  	if(exitBlock != null)	nodes.add((BasicBlock) exitBlock);
  	return new ControlFlowGraph(null, null, null, nodes, edges,
  			(BasicBlock) entryBlock, (BasicBlock) exitBlock, 
  			HashMultimap.<BasicBlock, Edge>create(), 
  			HashMultimap.<BasicBlock, Edge>create());  	
  }

	@Override
	public String toString() {
	  return name + "@" + sourceNode.getLocation().toString();
	}
	
	@Override
	public ControlFlowGraph clone() {
		Map<BasicBlock, BasicBlock> cloneMap = Maps.newHashMapWithExpectedSize(nodes.size());
		for(BasicBlock node : nodes) {
			cloneMap.put(node, node.clone());
		}
		
		assert (entry == null || cloneMap.containsKey(entry));
		assert (exit == null || cloneMap.containsKey(exit));
		
		BasicBlock entryClone = entry == null ? null : cloneMap.get(entry);
		BasicBlock exitClone = entry == null ? null : cloneMap.get(exit);
		ControlFlowGraph cfgClone = ControlFlowGraph.create(
				entryClone, exitClone);
		
		for(Edge edge : edges) {
			BasicBlock destClone = cloneMap.get(edge.getTarget());
			BasicBlock srcClone = cloneMap.get(edge.getSource());
			cfgClone.addEdge(srcClone, edge.getGuard(), destClone);
		}
		
		return cfgClone;
	}

	@Override
	public void format(Printer printer) {
	  printer
	      .p("CFG for: " + name + " (entry=" + getEntry().getId() + ")")
	      .incr();
	
	  for (BasicBlock block : getBlocks()) {
	    printer.pln();
	    formatBlock(printer, block);
	  }
	  printer.decr();
	}
	
	@Override
	public Set<Edge> getEdges() {
		return Collections.unmodifiableSet(edges);
	}
	
	@Override
	public Set<BasicBlock> getBlocks() {
	  return Collections.unmodifiableSet(nodes);
	}

	@Override
	public BasicBlock getEntry() {
	  return entry;
	}
	
	@Override
	public void setEntry(IRBasicBlock newEntry) {
		entry = (BasicBlock) newEntry;
	}
	
	@Override
	public void setExit(IRBasicBlock newExit) {
		exit = (BasicBlock) newExit;
	}

	@Override
	public BasicBlock getExit() {
	  return exit;
	}

	@Override
	public Location getLocation() {
		return sourceNode.getLocation();
	}

	@Override
	public String getName() {
	  return name;
	}

	@Override
	public Scope getScope() {
	  return scope;
	}

	@Override
	public Collection<Edge> getIncomingEdges(IRBasicBlock block) {
	  return Collections.unmodifiableCollection(incoming.get((BasicBlock) block));
	}

	@Override
	public Collection<Edge> getOutgoingEdges(IRBasicBlock block) {
	  return Collections.unmodifiableCollection(outgoing.get((BasicBlock) block));
	}

	@Override
	public Set<BasicBlock> getPredecessors(IRBasicBlock block) {
	  return Edge.getSources(getIncomingEdges(block));
	}

	@Override
	public Node getSourceNode() {
	  return sourceNode;
	}

	@Override
	public Set<BasicBlock> getSuccessors(IRBasicBlock block) {
	  return Edge.getTargets(getOutgoingEdges(block));
	}

	public BasicBlock newBlock(Scope scope) {
	  BasicBlock block = BasicBlock.create();
	  block.setScope(scope);
	  addNode(block);
	  return block;
	}	

	public BasicBlock newLabelBlock(Location loc, Scope scope) {
		BasicBlock block = BasicBlock.labelBlock(loc);
		block.setScope(scope);
		addNode(block);
		return block;
	}
	
	public BasicBlock newLabelBlock(Scope scope) {
		BasicBlock block = BasicBlock.labelBlock();
		block.setScope(scope);
		addNode(block);
		return block;
	}

	public BasicBlock newLoopBlock(Location loc, Scope scope) {
	  BasicBlock block = BasicBlock.loopBlock(loc);
	  block.setScope(scope);
	  addNode(block);
	  return block;
	}

	public BasicBlock newLoopInitBlock(Scope scope) {
	  BasicBlock block = BasicBlock.loopInitBlock();
	  block.setScope(scope);
	  addNode(block);
	  return block;
	}

	public BasicBlock newLoopExitBlock(Scope scope) {
	  BasicBlock block = BasicBlock.loopExitBlock();
	  block.setScope(scope);
	  addNode(block);
	  return block;
	}

	public BasicBlock newSwitchBlock(Location loc, Scope scope) {
	  BasicBlock block = BasicBlock.switchBlock(loc);
	  block.setScope(scope);
	  addNode(block);
	  return block;
	}

	@Override
	public void removeBlock(IRBasicBlock block) {
	  for( Edge e : ImmutableSet.copyOf(outgoing.get((BasicBlock) block)) ) {
	    removeEdge(e);
	  }
	  for( Edge e : ImmutableSet.copyOf(incoming.get((BasicBlock) block)) ) {
	    removeEdge(e);
	  }
	  nodes.remove(block);
	  
	  if(block == exit) exit = null;
	}

	@Override
	public void removeEdge(IREdge<?> edge) {
		outgoing.remove((BasicBlock) edge.getSource(), edge);
		incoming.remove((BasicBlock) edge.getTarget(), edge);
		edges.remove(edge);
	}

	@Override
	public void addEdge(IRBasicBlock currentBlock, IRBasicBlock succ) {
	  addEdge(Edge.create((BasicBlock) currentBlock, (BasicBlock) succ));
	}
	
	@Override
	public void addEdge(IRBasicBlock source, IRBooleanExpression guard,
	    IRBasicBlock target) {
	  addEdge(Edge.create((BasicBlock) source, guard, (BasicBlock) target));
	}
	
	@Override
	public void addEdge(IREdge<?> edge) {
		Preconditions.checkNotNull(edge.getSource());
		Preconditions.checkNotNull(edge.getTarget());
	  BasicBlock source = (BasicBlock) edge.getSource();
	  BasicBlock target = (BasicBlock) edge.getTarget();
	
	  addNode(source);
	  addNode(target);
	  /*
	   * addOutgoingEdge(source, edge); addIncomingEdge(target, edge);
	   */
	  outgoing.put(source, (Edge) edge);
	  incoming.put(target, (Edge) edge);
	  edges.add((Edge) edge);
	}

  @Override
	public Collection<IRBasicBlock> topologicalSeq(IRBasicBlock startBlock) {
		Collection<IRBasicBlock> sequence = Sets.newLinkedHashSetWithExpectedSize(nodes.size());
		Deque<IRBasicBlock> stack = Queues.newArrayDeque();
		stack.add(startBlock);
		
		Collection<IRBasicBlock> visiting = Sets.newHashSet();
		
		while(!stack.isEmpty()) {
			IRBasicBlock currBlock = stack.peek();
			if(visiting.contains(currBlock)) {
				stack.pop(); sequence.add(currBlock);
				continue;
			}
			
			visiting.add(currBlock);
			for(IREdge<?> out : getOutgoingEdges(currBlock)) {
				IRBasicBlock dest = out.getTarget();
				if(visiting.contains(dest)) continue;
				stack.push(dest);
			}
		}
		
		return sequence;
	}

	private boolean addNode(BasicBlock source) {
  	Preconditions.checkNotNull(source);
    if (nodes.contains(source)) return false;
    nodes.add(source);
    return true;
  }

  private void formatBlock(Printer printer, BasicBlock block) {
    block.format(printer);
    printer.incr();
    for (Edge edge : getOutgoingEdges(block)) {
      printer.indent().pln(edge.toString());
    }
    printer.decr();
  }
}
