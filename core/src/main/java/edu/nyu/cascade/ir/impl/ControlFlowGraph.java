package edu.nyu.cascade.ir.impl;

import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;

import xtc.tree.Location;
import xtc.tree.Node;
import xtc.tree.Printer;
import xtc.util.SymbolTable.Scope;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRBooleanExpression;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Pair;

public class ControlFlowGraph implements IRControlFlowGraph {
  private final Node sourceNode;
  private final String name;
  private final BasicBlock entry, exit;
  private final SortedSet<BasicBlock> nodes;
  private final Map<BasicBlock, Set<Edge>> incoming, outgoing;
  private final Scope scope;

  public ControlFlowGraph(Node sourceNode, String name, Scope scope) {
    this.sourceNode = sourceNode;
    this.name = name;
    this.scope = scope;

    entry = BasicBlock.entryBlock(sourceNode.getLocation());
    exit = BasicBlock.exitBlock();
    nodes = Sets.newTreeSet();
    incoming = Maps.newHashMap();
    outgoing = Maps.newHashMap();
    
  }

  public void addEdge(BasicBlock currentBlock, BasicBlock succ) {
    addEdge(Edge.create(currentBlock, succ));
  }

  public void addEdge(BasicBlock source, IRBooleanExpression guard,
      BasicBlock target) {
    addEdge(Edge.create(source, guard, target));
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

  private void addEdgeToMap(Map<BasicBlock, Set<Edge>> map,
      IRBasicBlock source, Edge edge) {
    // node should already exist
    assert (nodes.contains(source));
    Set<Edge> edges = map.get(source);
    // edges should be initialized in addNode
    assert (edges != null);
    /*
     * if (edges == null) { edges = Lists.newArrayList(); edgeMap.put(node,
     * edges); }
     */
    edges.add(edge);
  }

  private boolean addNode(BasicBlock source) {
    if (nodes.contains(source)) {
      return false;
    }
    nodes.add(source);
    incoming.put(source, Sets.<Edge> newHashSet());
    outgoing.put(source, Sets.<Edge> newHashSet());
    return true;
  }

  /*
   * Find the basic block in the CFG that "contains" the given position. If the
   * position falls "between" blocks, we choose the closest subsequent block if
   * <code>after</code> is <code>true</code> and the closest preceding block if
   * <code>after</code> is false.
   */
  public BasicBlock bestBlockForPosition(IRLocation loc/*
                                                         * , boolean
                                                         * insertBefore
                                                         */) {
    IOUtils.debug().pln("Finding block for location: " + loc).flush();

    int lineNum = loc.getLine();
    BasicBlock bestBlock = null;
    int bestDiff = Integer.MAX_VALUE;
    for (BasicBlock block : getBlocks()) {
      if (!block.hasLocation())
        continue;

      /*
       * List<? extends IRStatement> stmts = block.getStatements(); IRStatement
       * startStmt = stmts.get(0); IRStatement endStmt = stmts.get(stmts.size()
       * - 1);
       */
      IRLocation startLoc = block.getStartLocation();
      IRLocation endLoc = block.getEndLocation();

      assert (startLoc != null && endLoc != null);

      IOUtils.debug().p(block.toString() + ": ").flush();

      if (loc.isWithin(block)) {
        IOUtils.debug().pln("Exact match.");
        bestBlock = block;
        break;
      } else if (loc.precedes(block)) {
        int diff = startLoc.getLine() - lineNum;
        if (diff < bestDiff) {
          IOUtils.debug().pln("Best match so far. diff=" + diff);
          bestDiff = startLoc.getLine() - lineNum;
          bestBlock = block;
        } else {
          IOUtils.debug().pln("diff=" + diff);
        }
      } /*
         * else if (!insertBefore && loc.follows(block) && lineNum -
         * endLoc.getLine() < bestDiff) {
         * IOUtils.debug().pln("Best match so far."); bestDiff = lineNum -
         * endLoc.getLine(); bestBlock = block; }
         */else {
        IOUtils.debug().pln("Not a match.");
      }
    }
    if (bestBlock == null) {
      /* No block matched. Return the an extremal block. */
      IOUtils.debug().pln("No matching block found.").flush();
      // return insertBefore ? getExit() : getEntry();
      return getExit();
    } else {
      IOUtils.debug().pln("Block for location: " + bestBlock).flush();
      return bestBlock;
    }
  }

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
   * private void addIncomingEdge(BasicBlock node, Edge edge) { assert
   * (node.equals(edge.getTarget())); addEdgeToMap(incoming, node, edge); }
   */
  /*
   * void addInitialNode(BasicBlock block) { addNode(block);
   * initialNodes.add(block); }
   */
  
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
  public Set<Edge> getIncomingEdges(IRBasicBlock block) {
    assert (incoming.get(block) != null);
    return Collections.unmodifiableSet(incoming.get(block));
  }

  /*
   * public BasicBlock splitBlockAtPosition(IRBasicBlock irBlock, IRLocation
   * position) { Preconditions.checkArgument(irBlock instanceof BasicBlock);
   * Preconditions.checkArgument(nodes.contains(irBlock));
   * 
   * BasicBlock block = (BasicBlock) irBlock;
   * IOUtils.debug().pln("Splitting block " + block.getId()).flush();
   * 
   * BasicBlock succ = block.splitAt(position); // Make a copy so we can modify
   * the edge set Set<Edge> edgesToRemove =
   * Sets.newHashSet(outgoing.get(block)); for (Edge edge : edgesToRemove) {
   * removeEdge(edge); addEdge(succ, edge.getGuard(), edge.getTarget()); }
   * addEdge(block, succ); return succ; }
   */
  @Override
  public Location getLocation() {
    return sourceNode.getLocation();
  }

  @Override
  public String getName() {
    return name;
  }

  @Override
  public Set<Edge> getOutgoingEdges(IRBasicBlock block) {
    assert (outgoing.get(block) != null);
    return Collections.unmodifiableSet(outgoing.get(block));
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

  private void moveEdgesToSource(Set<Edge> edges, BasicBlock newSource) {
    // Make a copy so we can modify the edge set
    Set<Edge> edgesToRemove = Sets.newHashSet(edges);
    for (Edge edge : edgesToRemove) {
      removeEdge(edge);
      addEdge(newSource, edge.getGuard(), edge.getTarget());
    }
  }

  public BasicBlock newBlock(Scope scope) {
    BasicBlock block = BasicBlock.create();
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

  public BasicBlock newSwitchBlock(Location loc, Scope scope) {
    BasicBlock block = BasicBlock.switchBlock(loc);
    block.setScope(scope);
    addNode(block);
    return block;
  }

  public void removeBlock(BasicBlock block) {
    for( Edge e : ImmutableSet.copyOf(outgoing.get(block)) ) {
      removeEdge(e);
    }
    for( Edge e : ImmutableSet.copyOf(incoming.get(block)) ) {
      removeEdge(e);
    }
    nodes.remove(block);
  }

  public void removeEdge(Edge edge) {
    removeEdgeFromMap(outgoing, edge.getSource(), edge);
    removeEdgeFromMap(incoming, edge.getTarget(), edge);
  }

  private void removeEdgeFromMap(Map<BasicBlock, Set<Edge>> edgeMap,
      BasicBlock node, Edge edge) {
    Set<Edge> edges = edgeMap.get(node);
    // edges should be initialized in addNode
    assert (edges != null);
    edges.remove(edge);
  }

  @Override
  public Pair<BasicBlock, BasicBlock> splitAt(IRLocation position) {
    return splitAt(position, true);
  }

  @Override
  public Pair<BasicBlock, BasicBlock> splitAt(IRLocation position, boolean insertBefore) {
    BasicBlock block = bestBlockForPosition(position/* , insertBefore */);
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
      Set<Edge> inEdges = getIncomingEdges(block);
      if(inEdges.size() == 0) {
        IOUtils.debug().pln("Block unchanged.");
        return Pair.of(null, block);
      } else if (inEdges.size() == 1) {
        /*
         * Special case: if there's only one in-edge, we can re-configure the
         * CFG so that the position comes before it, at the cost of introducing
         * some non-determinism (since the guarded edge is no longer attached
         * directly to its source, and the dummy edge is unguarded).
         */
        assert (inEdges.iterator().hasNext());
        Edge e = inEdges.iterator().next();
        /* guard.loc <= block.loc && pos.loc < guard.loc */
        if (e.getGuard() != null && e.getGuard().getLocation().precedes(block)) {
          if(position.precedes(e.getGuard(), !insertBefore)) {
            /* Create a dummy predecessor */
            BasicBlock pred = e.getSource();
            BasicBlock dummy = newBlock(pred.getScope());

            removeEdge(e);
            addEdge(pred, dummy);
            addEdge(dummy, e.getGuard(), block);

            IOUtils.debug().pln("New blocks:");
            formatBlock(IOUtils.debug(), dummy);
            formatIncomingEdge(IOUtils.debug(), dummy);
            IOUtils.debug().pln();
            formatBlock(IOUtils.debug(), block);
            return Pair.of(dummy, block);
          } else {
            /* Create a dummy predecessor */
            BasicBlock pred = e.getSource();
            BasicBlock dummy = newBlock(pred.getScope());

            removeEdge(e);
            addEdge(pred, e.getGuard(), dummy);
            addEdge(dummy, block);

            IOUtils.debug().pln("New blocks:");
            formatBlock(IOUtils.debug(), dummy);
            formatIncomingEdge(IOUtils.debug(), dummy);
            IOUtils.debug().pln();
            formatBlock(IOUtils.debug(), block);
            return Pair.of(dummy, block);
          }
        } else {
          IOUtils.debug().pln("Block unchanged.");
          return Pair.of(e.getSource(), block);
        }
      } else {
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
        IOUtils.debug().pln("New blocks:");
        formatBlock(IOUtils.debug(), dummy);
        formatIncomingEdge(IOUtils.debug(), dummy);
        IOUtils.debug().pln();
        formatBlock(IOUtils.debug(), block);
        return Pair.of(dummy, block);
        
//        IOUtils.debug().pln("Block unchanged.");
//        return Pair.of(null, block);
      }
    }
    
    /*
     * If the position follows the block and comes before all incoming edge
     * guards, we can just create a dummy successor. If it comes after any
     * outgoing edge guards, we have would have to significantly re-structure
     * the CFG to accomplish the split, so we just return <code>null</code> (to
     * signal failure).
     */
    if (position.follows(block, insertBefore)) {
      Set<Edge> outEdges = getOutgoingEdges(block);
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

      IOUtils.debug().pln("New blocks:");
      formatBlock(IOUtils.debug(), block);
      IOUtils.debug().pln();
      formatBlock(IOUtils.debug(), dummy);
      formatIncomingEdge(IOUtils.debug(), dummy);
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

    IOUtils.debug().pln("New blocks:");
    formatBlock(IOUtils.debug(), block);
    IOUtils.debug().pln();
    formatBlock(IOUtils.debug(), dummy);
    formatIncomingEdge(IOUtils.debug(), dummy);
    return Pair.of(block, dummy);
  }

  @Override
  public String toString() {
    return name + "@" + sourceNode.getLocation().toString();
  }

  @Override
  public Scope getDefiningScope() {
    return scope.getParent();
  }

  @Override
  public Scope getScope() {
    return scope;
  }

}
