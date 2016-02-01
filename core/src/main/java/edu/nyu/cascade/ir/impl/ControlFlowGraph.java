package edu.nyu.cascade.ir.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.List;
import java.util.Set;
import java.util.SortedSet;

import xtc.tree.Location;
import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.Queues;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRBooleanExpression;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;

public class ControlFlowGraph implements IRControlFlowGraph {
  private final Node sourceNode;
  private final String name;
  private final BasicBlock entry, exit;
  private final SortedSet<BasicBlock> nodes;
  private final Multimap<BasicBlock, Edge> incoming, outgoing;
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
    incoming = HashMultimap.create();
    outgoing = HashMultimap.create();
    
  }
  
  /**
   * Create a new CFG without any function source node attached
   * @param entryBlock
   * @param exitBlock
   */
  public ControlFlowGraph(IRBasicBlock entryBlock, IRBasicBlock exitBlock) {
  	sourceNode = null;
  	name = null;
  	scope = null;
  	
  	entry = (BasicBlock) entryBlock;
  	exit = (BasicBlock) exitBlock;
  	
  	nodes = Sets.newTreeSet();
  	nodes.add((BasicBlock) entryBlock);
  	nodes.add((BasicBlock) exitBlock);
  	
  	incoming = HashMultimap.create();
  	outgoing = HashMultimap.create();
  }
  
  /**
	 * Find a path map in the CFG to the given start block and target block and 
	 * store it in cfg.
	 * @return empty map if no path has been found
	 */
  @Override
	public IRControlFlowGraph findPathsBtwnBlocks(IRBasicBlock start, IRBasicBlock target) {
		boolean isLoop = start == target;
		
		ControlFlowGraph freshCFG = new ControlFlowGraph(start, target);
		
	  Deque<List<Edge>> queue = Queues.newArrayDeque();
	  for (Edge ve : getIncomingEdges(target)) {
	  	List<Edge> path = Lists.<Edge>newArrayList(ve);
	  	queue.add(path);
	  }
	  
	  while(!queue.isEmpty()) {
	    List<Edge> edges = queue.poll();
	    assert !edges.isEmpty();
	    /* get the source node from the newly-added edge */
	    IRBasicBlock head = edges.get(0).getSource();
	    /* reach the start node */
	    if(head.equals(start)) {
	    	for(Edge edge : edges) freshCFG.addEdge(edge);
	    } else {
	      for(Edge ve :getIncomingEdges(head)) {
	        final IRBasicBlock src = ve.getSource();
	        
	        if(isLoop) {
	        	boolean isWithinScope = src.getScope().getQualifiedName().startsWith(
		        		start.getScope().getQualifiedName());
		        if(!isWithinScope) continue;
	        }
	        
	        boolean visited = Iterables.any(edges, new Predicate<IREdge<?>>(){
	          @Override
	          public boolean apply(IREdge<?> edge) {
	           return edge.getTarget().equals(src); 
	          }
	        });
	        
	        if(visited && src != start) continue; // if src == start, ve is loop back edge
	        
	        List<Edge> edgesPrime = Lists.<Edge>newArrayList(ve);
	        edgesPrime.addAll(edges);
	        queue.add(edgesPrime);
	      }
	    }
	  }
	  return freshCFG;
	}

	public static Collection<IRBasicBlock> topologicalSeq(IRControlFlowGraph cfg) {
		Collection<IRBasicBlock> seq = Lists.newArrayList();
		Deque<IRBasicBlock> stack = Queues.newArrayDeque();
		stack.add(cfg.getEntry());
		
		Collection<IRBasicBlock> visiting = Sets.newHashSet();
		
		while(!stack.isEmpty()) {
			IRBasicBlock currBlock = stack.peek();
			if(visiting.contains(currBlock)) {
				stack.pop(); seq.add(currBlock);
				continue;
			}
			
			visiting.add(currBlock);
			for(IREdge<?> out : cfg.getOutgoingEdges(currBlock)) {
				IRBasicBlock dest = out.getTarget();
				if(visiting.contains(dest)) continue;
				stack.push(dest);
			}
		}
		
		return seq;
	}
	
	public static boolean deleteDeadBlocks(IRControlFlowGraph cfg) {
		Collection<IRBasicBlock> topologicSeq = topologicalSeq(cfg);
		Collection<IRBasicBlock> deadBlocks = Lists.newArrayList(cfg.getBlocks());
		deadBlocks.removeAll(topologicSeq); // remained are dead blocks;
		if(deadBlocks.isEmpty()) return false;
		
		for(IRBasicBlock block : deadBlocks) cfg.removeBlock(block);
		return true;
	}

	@Override
	public String toString() {
	  return name + "@" + sourceNode.getLocation().toString();
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

	/*
	 * private void addOutgoingEdge(BasicBlock node, Edge edge) { assert
	 * (node.equals(edge.getSource())); addEdgeToMap(outgoing, node, edge); }
	 */
	@Override
	public Set<BasicBlock> getBlocks() {
	  return Collections.<BasicBlock> unmodifiableSet(nodes);
	}

	@Override
	public BasicBlock getEntry() {
	  return entry;
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
	public Scope getDefiningScope() {
	  return scope.getParent();
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

	@Override
	public BasicBlock bestBlockForPosition(final IRLocation loc) {
		return bestBlockForPosition(loc, false);
	}
	
	@Override
	public boolean isEmpty() {
		return incoming.isEmpty() && outgoing.isEmpty();
	}
	
	/**
	 * Find the basic block in the CFG that "contains" the given position. If the
	 * position falls "between" blocks, we choose the closest subsequent block if
	 * <code>after</code> is <code>true</code> and the closest preceding block if
	 * <code>after</code> is false.
	 */
	@Override
	public BasicBlock bestBlockForPosition(final IRLocation loc, boolean isLoopPos) {
		Preconditions.checkNotNull(loc);
	  
		IOUtils.debug().pln("Finding block for location: " + loc).flush();
	  
		if(isLoopPos) return bestLoopBlockForPosition(loc);
	  
	  Iterable<BasicBlock> bestBlocks = Iterables.filter(getBlocks(), 
	  		new Predicate<BasicBlock>() {
					@Override
          public boolean apply(BasicBlock block) {
	          if(loc.isWithin(block)) {
	          	IOUtils.debug().p(block + ": ").flush();
	    	      IOUtils.debug().pln("Exact match.");
	    	      return true;
	          }
	          
	          return false;
          }
	  });
	  
	  if(!Iterables.isEmpty(bestBlocks)) {
	  	if(Iterables.size(bestBlocks) > 1)
	  		IOUtils.debug().pln("WARNING: more matching blocks for location: " + loc);
	  	return bestBlocks.iterator().next();
	  }
	  
	  int lineNum = loc.getLine();
	  int bestDiff = Integer.MAX_VALUE;
	  
	  BasicBlock bestBlock = null;
	  
	  for (BasicBlock block : getBlocks()) {
	    if (!block.hasLocation()) continue;
	
	    IOUtils.debug().p(block + ": ").flush();
	
	    if (loc.precedes(block)) {
		    IRLocation startLoc = block.getStartLocation();
	      int diff = startLoc.getLine() - lineNum;
	      if (diff < bestDiff) {
	        IOUtils.debug().pln("Best match so far. diff=" + diff);
	        bestDiff = startLoc.getLine() - lineNum;
	        bestBlock = block;
	      } else {
	        IOUtils.debug().pln("diff=" + diff);
	      }
	    }
	  }
	  
	  if(bestBlock != null) {
	    IOUtils.debug().pln("Block for location: " + bestBlock).flush();
	    return bestBlock;
	  }
	  
	  /* No block matched. Return the an extremal block. */
	  IOUtils.debug().pln("No matching block found.").flush();
	  return getExit();
	}

	private BasicBlock bestLoopBlockForPosition(IRLocation loc) {
		Preconditions.checkNotNull(loc);
	  
	  List<BasicBlock> betterBlocks = Lists.newArrayList();
	  for (BasicBlock block : getBlocks()) {
	    if (!block.hasLocation())		continue;
	
	    IOUtils.debug().p(block.toString() + ": ").flush();
	
	    if (loc.isWithin(block)) {
	      IOUtils.debug().pln("Exact match.");
	      betterBlocks.add(block);
	    }
	  }
	  
	  Iterable<BasicBlock> betterLoopBlocks = Iterables.filter(betterBlocks, 
	  		new Predicate<BasicBlock>(){
			@Override
	    public boolean apply(BasicBlock block) {
	      return block.getType().equals(IRBasicBlock.Type.LOOP);
	    }
	  });
	  
	  if (Iterables.isEmpty(betterBlocks)) {
	    /* No block matched. Return the an exit block. */
	    IOUtils.err().println("WARNING: no matching block found.");
	    return getExit();
	  }
	  
	  if(Iterables.isEmpty(betterLoopBlocks)) {
	    /* No block matched. Return the an exit block. */
	    IOUtils.debug().pln("WARNING: no matching loop block found.").flush();
	    return Iterables.get(betterBlocks, 0);
	  } 
	  
	  assert(Iterables.size(betterLoopBlocks) == 1);
	  BasicBlock bestBlock = betterLoopBlocks.iterator().next();
	  IOUtils.debug().pln("Loop block for location: " + bestBlock).flush();
	  return bestBlock;
	}

	@Override
	public Pair<? extends IRBasicBlock, ? extends IRBasicBlock> splitAt(IRLocation position) {
	  return splitAt(position, true);
	}

	@Override
	public Pair<? extends IRBasicBlock, ? extends IRBasicBlock> splitAt(
			IRLocation position, boolean insertBefore) {
	  return splitAt(position, false, insertBefore);
	}

	@Override
	public Pair<? extends IRBasicBlock, ? extends IRBasicBlock> splitAt(
	    IRLocation location, boolean isLoopPos, boolean insertBefore) {
	  BasicBlock block = isLoopPos ? bestLoopBlockForPosition(location) : 
	  	bestBlockForPosition(location);
	  return splitAtBlock(block, location, insertBefore);
	}

	@Override
	public void insertAt(IRLocation loc, 
			List<IRStatement> stmts, 
			boolean isLoop, 
			boolean insertBefore) {
		Pair<? extends IRBasicBlock, ? extends IRBasicBlock> pair = splitAt(loc, isLoop, insertBefore);
		BasicBlock fst = (BasicBlock) pair.fst();
		final BasicBlock snd = (BasicBlock) pair.snd();
		
		Edge edge = Iterables.find(getOutgoingEdges(fst), new Predicate<Edge>(){
			@Override
			public boolean apply(Edge edge) {
				return snd.equals(edge.getTarget());
			}
		});
		
		Scope scope = snd.getScope();
		BasicBlock freshBlock = newBlock(scope);
		freshBlock.addStatements(stmts);
		
		removeEdge(edge);
		addEdge(fst, freshBlock);
		addEdge(freshBlock, snd);
		
		printFormatBlocks(fst, freshBlock);
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
	}

	@Override
	public void removeEdge(IREdge<?> edge) {
	  removeEdgeFromMap(outgoing, (BasicBlock) edge.getSource(), edge);
	  removeEdgeFromMap(incoming, (BasicBlock) edge.getTarget(), edge);
	}

	public void addEdge(BasicBlock currentBlock, BasicBlock succ) {
	  addEdge(Edge.create(currentBlock, succ));
	}

	public void addEdge(BasicBlock source, IRBooleanExpression guard,
	    BasicBlock target) {
	  addEdge(Edge.create(source, guard, target));
	}
	
	private void removeEdgeFromMap(Multimap<BasicBlock, Edge> edgeMap,
	    BasicBlock node, IREdge<?> edge) {
	  Collection<Edge> edges = edgeMap.get(node);
	  edges.remove(edge);
	}

	private void addEdge(Edge edge) {
    BasicBlock source = edge.getSource();
    BasicBlock target = edge.getTarget();

    addNode(source);
    addNode(target);
    /*
     * addOutgoingEdge(source, edge); addIncomingEdge(target, edge);
     */
    addEdgeToMap(outgoing, source, edge);
    addEdgeToMap(incoming, target, edge);
  }

  private void addEdgeToMap(Multimap<BasicBlock, Edge> edgeMap,
      BasicBlock source, Edge edge) {
    // node should already exist
    assert (nodes.contains(source));
    Collection<Edge> edges = edgeMap.get(source);
    edges.add(edge);
  }

  private boolean addNode(BasicBlock source) {
    if (nodes.contains(source)) return false;
    nodes.add(source);
    return true;
  }

  private void formatIncomingEdge(Printer printer, BasicBlock block) {
    printer.incr();
    for (Edge edge : getIncomingEdges(block)) {
      printer.indent().pln(edge.toString());
    }
    printer.decr();
  }

  private void formatBlock(Printer printer, BasicBlock block) {
    block.format(printer);
    printer.incr();
    for (Edge edge : getOutgoingEdges(block)) {
      printer.indent().pln(edge.toString());
    }
    printer.decr();
  }

  private void moveEdgesToSource(Collection<Edge> collection, BasicBlock newSource) {
    // Make a copy so we can modify the edge set
    Set<Edge> edgesToRemove = Sets.newHashSet(collection);
    for (Edge edge : edgesToRemove) {
      removeEdge(edge);
      addEdge(newSource, edge.getGuard(), edge.getTarget());
    }
  }

  private Pair<BasicBlock, BasicBlock> splitAtBlock(BasicBlock block, IRLocation position, 
  		boolean insertBefore) {
  	
    IOUtils
        .debug()
        .pln(
            "Splitting block " + block.getId() + (insertBefore ? " before " : " after ")
                + position.toString())
        .flush();
    
    /*
     * If the position precedes the block and comes after all incoming edge
     * guards, we're fine. If it comes before any incoming edge guards, we have
     * would have to significantly re-structure the CFG to accomplish the split,
     * so we just return <code>null</code> (to signal failure).
     */
    if (position.precedes(block, !insertBefore)) {
      Collection<Edge> inEdges = getIncomingEdges(block);
      
      if(inEdges.size() == 0) {
        IOUtils.debug().pln("Block unchanged.");
        return Pair.of(null, block);
      } 
      
      if (inEdges.size() == 1) {
        /*
         * Special case: if there's only one in-edge, we can re-configure the
         * CFG so that the position comes before it, at the cost of introducing
         * some non-determinism (since the guarded edge is no longer attached
         * directly to its source, and the dummy edge is unguarded).
         */
        assert (inEdges.iterator().hasNext());
        Edge e = inEdges.iterator().next();
        
        /* guard.loc > block.loc */
        if(e.getGuard() == null || e.getGuard().getLocation().strictFollows(block)) {
          IOUtils.debug().pln("Block unchanged.");
          return Pair.of(e.getSource(), block);
        }
        
        /* guard.loc <= block.loc */
        
        /* pos.loc < guard.loc */
        if(position.precedes(e.getGuard(), !insertBefore)) {
          /* Create a dummy predecessor */
          BasicBlock pred = e.getSource();
          BasicBlock dummy = newBlock(pred.getScope());

          removeEdge(e);
          addEdge(pred, dummy);
          addEdge(dummy, e.getGuard(), block);

          printFormatBlocks(block, dummy);
          return Pair.of(dummy, block);
        } 

        /* pos.loc >= guard.loc */
        BasicBlock pred = e.getSource();
        /* Create a dummy predecessor */
        BasicBlock dummy = newBlock(pred.getScope());
        
        removeEdge(e);
        addEdge(pred, e.getGuard(), dummy);
        addEdge(dummy, block);
        
        printFormatBlocks(block, dummy);
        return Pair.of(dummy, block);
      } 
      
      /* We have more than one edge. All must come before position. */
      for (Edge e : inEdges) {
        if (e.getGuard() != null
            && position.precedes(e.getGuard(), !insertBefore)) {
          IOUtils
              .debug()
              .pln("Bad split. Position precedes a guard.")
              .flush();
          return null; // give up
        }
      }
      
      BasicBlock dummy = newBlock(block.getScope());
      for(Object o : inEdges.toArray()) {
        Edge e = (Edge) o;
        removeEdge((Edge)e);
        addEdge(e.getSource(), e.getGuard(), dummy);
      }
      addEdge(dummy, block);
      
      printFormatBlocks(block, dummy);
      return Pair.of(dummy, block);
    }
    
    /*
     * If the position follows the block and comes before all incoming edge
     * guards, we can just create a dummy successor. If it comes after any
     * outgoing edge guards, we have would have to significantly re-structure
     * the CFG to accomplish the split, so we just return <code>null</code> (to
     * signal failure).
     */
    if (position.follows(block, insertBefore)) {
      Collection<Edge> outEdges = getOutgoingEdges(block);
      for (Edge e : outEdges) {
        if (e.getGuard() != null && e.getGuard().getLocation().strictFollows(block)
            && position.follows(e.getGuard(), insertBefore)) {
          IOUtils.debug().pln("Bad split. Position follows a guard.").flush();
          return null; // give up
        }
      }
      
      if(outEdges.size() == 1) {
        /*
         * Special case: if there's only one out-edge, we can re-configure the
         * CFG so that the position comes before it, at the cost of introducing
         * some non-determinism (since the guarded edge is no longer attached
         * directly to its source, and the dummy edge is unguarded).
         */
        assert (outEdges.iterator().hasNext());
        Edge e = outEdges.iterator().next();
        if (e.getGuard() == null) {
          IOUtils.debug().pln("Block unchanged.");
          return Pair.of(block, e.getTarget());
        }
      }
      
      /* Create a dummy node after block, which will come *after* position. */
      BasicBlock dummy = newBlock(block.getScope());
      moveEdgesToSource(getOutgoingEdges(block), dummy);
      
      addEdge(block, dummy);
      
      printFormatBlocks(block, dummy);
      return Pair.of(block, dummy);
    }

    /* The position neither precedes nor follows the block. I.e., we have to 
     * split the block in the middle.
     */
    assert (position.isWithin(block));
    BasicBlock dummy = insertBefore ? block.splitBefore(position) : block
        .splitAfter(position);

    moveEdgesToSource(getOutgoingEdges(block), dummy);
    addEdge(block, dummy);

    printFormatBlocks(block, dummy);
    return Pair.of(block, dummy);
  }

  private void printFormatBlocks(BasicBlock block, BasicBlock dummy) {
    IOUtils.debug().pln("New blocks:");
    formatBlock(IOUtils.debug(), block);
    IOUtils.debug().pln();
    formatBlock(IOUtils.debug(), dummy);
    formatIncomingEdge(IOUtils.debug(), dummy);
  }
}
