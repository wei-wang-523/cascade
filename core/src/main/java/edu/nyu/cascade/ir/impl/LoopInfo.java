package edu.nyu.cascade.ir.impl;

import java.util.Collection;
import java.util.Deque;
import java.util.Map;

import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;
import com.google.common.collect.Queues;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;

public class LoopInfo {
	// Mapping of basic blocks to the inner most loop they occur in
	private final Map<IRBasicBlock, Loop> innerLoopMap;
	// All the top-level tops without parent loop
	private final Collection<Loop> topLevelLoops;
	
	private LoopInfo(IRControlFlowGraph cfg) {
		DominatorTree domTree = DominatorTree.analyze(cfg);
		Map<IRBasicBlock, Loop> innerLoopMap = Maps.newHashMap();
		Collection<Loop> topLevelLoops = Sets.newHashSet();
		analyze(cfg, domTree, innerLoopMap, topLevelLoops);		
		this.innerLoopMap = innerLoopMap;
		this.topLevelLoops = topLevelLoops;
	}
	
	public static LoopInfo analyze(IRControlFlowGraph cfg) {
		return new LoopInfo(cfg);
	}
	
	public Map<IRBasicBlock, Loop> getInnerLoopMap() {
	  return innerLoopMap;
	}

	public Collection<Loop> getTopLevelLoops() {
	  return topLevelLoops;
	}

	/**
	 * Analyze LoopInfo discovers loops during a postorder DominatorTree traversal
	 * interleaved with backward CFG traversals within each subloop
	 * (discoverAndMapSubloop). The backward traversal skips inner subloops, so
	 * this part of the algorithm is linear in the number of CFG edges. Subloop and
	 * blocks are then populated during a single forward CFG traversal.
	 * 
	 * During the two CFG traversals each block is seen three times:
	 * 1) Discovered and mapped by a reverse CFG traversal.
	 * 2) Visited during a forward DFS CFG traversal.
	 * 3) Reverse-inserted in the loop in postorder following forward DFS.
	 * 
	 * The Block vectors are inclusive, so step 3 requires loop-depth number of
	 * insertions per block.
	 * 
	 * @param cfg
	 * @param domTree
	 * @return
	 */
	private void analyze(IRControlFlowGraph cfg, 
			final DominatorTree domTree,
			Map<IRBasicBlock, Loop> innerLoopMap,
			Collection<Loop> topLevelLoops) {

		for(final IRBasicBlock potentialHeader : domTree.getBlocks()) {
			Iterable<? extends IREdge<? extends IRBasicBlock>> backEdges = Iterables.filter(
					cfg.getIncomingEdges(potentialHeader), new Predicate<IREdge<?>>() {
						@Override
            public boolean apply(IREdge<?> edge) {
							IRBasicBlock src = edge.getSource();
							return domTree.dominates(potentialHeader, src);
            }
					});
			
			if(!Iterables.isEmpty(backEdges)) {
				Loop loop = new Loop(cfg, potentialHeader);
				discoverAndMapSubloop(cfg, domTree, innerLoopMap, loop, backEdges);
			}
		}
		
		propagateLoopsDFS(cfg, innerLoopMap, topLevelLoops);
	}
	
	private void propagateLoopsDFS(IRControlFlowGraph cfg,
			Map<IRBasicBlock, Loop> innerLoopMap,
			Collection<Loop> topLevelLoops) {
		Deque<IRBasicBlock> stack = Queues.newArrayDeque();
		stack.push(cfg.getEntry());
		Collection<IRBasicBlock> visited = Sets.newHashSet();
		visited.add(cfg.getEntry());
		while(!stack.isEmpty()) {
			while(true) {
				IRBasicBlock stackTop = stack.peek();
				boolean newlyPushed = false;
				for(IREdge<?> edge : cfg.getOutgoingEdges(stackTop)) {
					IRBasicBlock dest = edge.getTarget();
					if(visited.contains(dest)) continue;
					// Push the next DFS successor onto the stack.
					stack.push(dest); newlyPushed = true;
				}
				if(!newlyPushed) break;
			}
			
			// Visit the top of the stack in postorder and backtrack.			
			IRBasicBlock stackTop = stack.peek();
			insertIntoLoop(innerLoopMap, topLevelLoops, stackTop);
			stack.pop();
		}
	}

	/**
	 * Add a single Block to its ancestor loops in PostOrder. If the block is a
	 * subloop header, add the subloop to its parent in PostOrder, then reverse the
	 * Blocks and Subloops of the now complete subloop to achieve RPO.
	 * @param block
	 */
	private void insertIntoLoop(Map<IRBasicBlock, Loop> innerLoopMap,
			Collection<Loop> topLevelLoops,
			IRBasicBlock block) {
		if(!innerLoopMap.containsKey(block)) return;
		Loop subLoop = innerLoopMap.get(block);
		if(block == subLoop.getHeader()) {
			// We reach this point once per sub-loop after processing all the blocks in the sub-loop
			if(subLoop.getParent() != null) {
				subLoop.getParent().addSubLoop(subLoop);
			} else {
				topLevelLoops.add(subLoop);
			}
			
			subLoop = subLoop.getParent();
		}
		
		while(subLoop != null) {
			subLoop.addBlock(block);
			subLoop = subLoop.getParent();
		}
	}
	
	/**
	 * Discover a subloop with the specified backedges such that: All blocks within
	 * this loop are mapped to this loop or a subloop. And all subloops within this
	 * loop have their parent loop set to this loop or a subloop.
	 */
	private void discoverAndMapSubloop(IRControlFlowGraph cfg, 
			DominatorTree domTree, 
			Map<IRBasicBlock, Loop> innerLoopMap,
			Loop loop, 
			Iterable<? extends IREdge<? extends IRBasicBlock>> backEdges) {
		int numBlocks = 0, numSubLoops = 0;
		
		Deque<IREdge<?>> backEdgesWorkList = Queues.newArrayDeque();
		for(IREdge<?> backEdge : backEdges) backEdgesWorkList.push(backEdge);
		
		while(!backEdgesWorkList.isEmpty()) {
			IREdge<?> backEdge = backEdgesWorkList.pop();
			IRBasicBlock src = backEdge.getSource();
			
			if(!innerLoopMap.containsKey(src)) {
				// This is an undiscovered block. Map it to the current loop.
				innerLoopMap.put(src, loop);
				++numBlocks;
				
				if(src.equals(loop.getHeader())) continue;
				
				// Push all block's incoming edges on the back edge worklist.
				for(IREdge<?> incoming : cfg.getIncomingEdges(src))
					backEdgesWorkList.push(incoming);
				
			} else {
				// This is a discovered block. Find its outermost discovered loop.
				Loop subLoop = innerLoopMap.get(src); // inner most loop
				while(subLoop.getParent() != null) 
					subLoop = subLoop.getParent();
				
				// If it is already discovered to be a subloop of this loop, continue.
				if(subLoop == loop) continue;
				
				// Discover a subloop of this loop.
				subLoop.setParent(loop);
				++numSubLoops;
				
				numBlocks += subLoop.getBlocks().size();
				IRBasicBlock subHeader = subLoop.getHeader();
				
				// Continue traversal along predecessors that are not loop-back edges from
				// within this subloop tree itself. Note that a predecessor may directly
				// reach another subloop that is not yet discovered to be a subloop of
				// this loop, which we must traverse.
				// Push all block's incoming edges on the back edge deque.
				for(IREdge<?> incoming : cfg.getIncomingEdges(subHeader)) {
					IRBasicBlock preSubHeader = incoming.getSource();
					if(innerLoopMap.get(preSubHeader) != subLoop)
						backEdgesWorkList.push(incoming);
				}
			}
		}
		
		loop.setNumBlocks(numBlocks);
		loop.setNumSubLoops(numSubLoops);
	}
}
