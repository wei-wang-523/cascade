package edu.nyu.cascade.ir.impl;

import java.util.Collection;
import java.util.Deque;
import java.util.Map;
import java.util.Set;

import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Queues;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;

public class LoopInfoUtil {
	public static LoopInfo analyze(IRControlFlowGraph cfg) {
		Map<IRBasicBlock, Loop> innerLoopMap = Maps.newHashMap();
		Collection<Loop> topLevelLoops = Sets.newHashSet();
		analyzeNatural(cfg, innerLoopMap, topLevelLoops);
		return new LoopInfo(innerLoopMap, topLevelLoops);
	}

	public static Loop getLoop(IRControlFlowGraph cfg,
	    final IRBasicBlock loopHeader) {
		final DominatorTree domTree = DominatorTree.analyze(cfg, loopHeader);
		Iterable<? extends IREdge<? extends IRBasicBlock>> backEdges = Iterables
		    .filter(cfg.getIncomingEdges(loopHeader), new Predicate<IREdge<?>>() {
			    @Override
			    public boolean apply(IREdge<?> edge) {
				    IRBasicBlock src = edge.getSource();
				    return domTree.dominates(loopHeader, src);
			    }
		    });

		Loop loop = new Loop(cfg, loopHeader);
		Deque<IREdge<?>> backEdgesWorkList = Queues.newArrayDeque();
		for (IREdge<?> backEdge : backEdges)
			backEdgesWorkList.push(backEdge);

		while (!backEdgesWorkList.isEmpty()) {
			IREdge<?> backEdge = backEdgesWorkList.pop();
			IRBasicBlock src = backEdge.getSource();
			loop.addBlock(src);
			if (src.equals(loop.getHeader()))
				continue;
			// Push all block's incoming edges on the back edge worklist.
			for (IREdge<?> incoming : cfg.getIncomingEdges(src))
				backEdgesWorkList.push(incoming);
		}
		return loop;
	}

	/**
	 * Analyze LoopInfo discovers loops during a postorder DominatorTree traversal
	 * interleaved with backward CFG traversals within each subloop
	 * (discoverAndMapSubloop). The backward traversal skips inner subloops, so
	 * this part of the algorithm is linear in the number of CFG edges. Subloop
	 * and blocks are then populated during a single forward CFG traversal.
	 * 
	 * During the two CFG traversals each block is seen three times: 1) Discovered
	 * and mapped by a reverse CFG traversal. 2) Visited during a forward DFS CFG
	 * traversal. 3) Reverse-inserted in the loop in postorder following forward
	 * DFS.
	 * 
	 * The Block vectors are inclusive, so step 3 requires loop-depth number of
	 * insertions per block.
	 * 
	 * @param cfg
	 * @param domTree
	 * @return
	 */
	static void analyzeNatural(IRControlFlowGraph cfg,
	    Map<IRBasicBlock, Loop> innerLoopMap, Collection<Loop> topLevelLoops) {
		final DominatorTree domTree = DominatorTree.analyze(cfg);

		Collection<IRBasicBlock> postOrderSeq = Lists.reverse(domTree.getBlocks());
		for (final IRBasicBlock potentialHeader : postOrderSeq) {
			Iterable<? extends IREdge<? extends IRBasicBlock>> backEdges = Iterables
			    .filter(cfg.getIncomingEdges(potentialHeader),
			        new Predicate<IREdge<?>>() {
				        @Override
				        public boolean apply(IREdge<?> edge) {
					        IRBasicBlock src = edge.getSource();
					        return domTree.dominates(potentialHeader, src);
				        }
			        });

			if (!Iterables.isEmpty(backEdges)) {
				Loop loop = new Loop(cfg, potentialHeader);
				discoverAndMapSubloopNatural(cfg, innerLoopMap, loop, backEdges);
			}
		}

		/*
		 * Perform a single forward CFG traversal to populate block and subloop list
		 * for all loops
		 */
		for (IRBasicBlock block : postOrderSeq) {
			insertIntoLoop(innerLoopMap, topLevelLoops, block);
		}
	}

	/**
	 * Analyze LoopInfo discovers loops during a postorder DominatorTree traversal
	 * interleaved with backward CFG traversals within each subloop
	 * (discoverAndMapSubloop). The backward traversal skips inner subloops, so
	 * this part of the algorithm is linear in the number of CFG edges. Subloop
	 * and blocks are then populated during a single forward CFG traversal.
	 * 
	 * During the two CFG traversals each block is seen three times: 1) Discovered
	 * and mapped by a reverse CFG traversal. 2) Visited during a forward DFS CFG
	 * traversal. 3) Reverse-inserted in the loop in postorder following forward
	 * DFS.
	 * 
	 * The Block vectors are inclusive, so step 3 requires loop-depth number of
	 * insertions per block.
	 * 
	 * @param cfg
	 * @param domTree
	 * @return
	 */
	static void analyzeUnnatural(IRControlFlowGraph cfg,
	    Map<IRBasicBlock, Loop> innerLoopMap, Collection<Loop> topLevelLoops) {

		final Collection<IREdge<?>> backEdgeDFS = detectBackEdges(cfg);
		Collection<IRBasicBlock> postOrderSeq = cfg.topologicalSeq(cfg.getEntry());

		for (final IRBasicBlock potentialHeader : postOrderSeq) {
			Iterable<? extends IREdge<? extends IRBasicBlock>> backEdges = Iterables
			    .filter(cfg.getIncomingEdges(potentialHeader),
			        new Predicate<IREdge<?>>() {
				        @Override
				        public boolean apply(IREdge<?> edge) {
					        return backEdgeDFS.contains(edge);
				        }
			        });

			if (!Iterables.isEmpty(backEdges)) {
				Loop loop = new Loop(cfg, potentialHeader);
				discoverAndMapSubloopUnnatural(cfg, innerLoopMap, loop, backEdges);
			}
		}

		/*
		 * Perform a single forward CFG traversal to populate block and subloop list
		 * for all loops
		 */
		for (IRBasicBlock block : postOrderSeq) {
			insertIntoLoop(innerLoopMap, topLevelLoops, block);
		}
	}

	/**
	 * Add a single Block to its ancestor loops in PostOrder. If the block is a
	 * subloop header, add the subloop to its parent in PostOrder, then reverse
	 * the Blocks and Subloops of the now complete subloop to achieve RPO.
	 * 
	 * @param block
	 */
	private static void insertIntoLoop(Map<IRBasicBlock, Loop> innerLoopMap,
	    Collection<Loop> topLevelLoops, IRBasicBlock block) {
		if (!innerLoopMap.containsKey(block))
			return;
		Loop subLoop = innerLoopMap.get(block);
		if (block == subLoop.getHeader()) {
			// We reach this point once per sub-loop after processing all the blocks
			// in the sub-loop
			if (subLoop.getParent() != null) {
				subLoop.getParent().addSubLoop(subLoop);
			} else {
				topLevelLoops.add(subLoop);
			}

			subLoop = subLoop.getParent();
		}

		while (subLoop != null) {
			subLoop.addBlock(block);
			subLoop = subLoop.getParent();
		}
	}

	/**
	 * Discover a subloop with the specified backedges such that: All blocks
	 * within this loop are mapped to this loop or a subloop. And all subloops
	 * within this loop have their parent loop set to this loop or a subloop.
	 */
	private static void discoverAndMapSubloopNatural(IRControlFlowGraph cfg,
	    Map<IRBasicBlock, Loop> innerLoopMap, Loop loop,
	    Iterable<? extends IREdge<? extends IRBasicBlock>> backEdges) {
		int numBlocks = 0, numSubLoops = 0;

		Deque<IREdge<?>> backEdgesWorkList = Queues.newArrayDeque();
		for (IREdge<?> backEdge : backEdges)
			backEdgesWorkList.push(backEdge);

		while (!backEdgesWorkList.isEmpty()) {
			IREdge<?> backEdge = backEdgesWorkList.pop();
			IRBasicBlock src = backEdge.getSource();

			if (!innerLoopMap.containsKey(src)) {
				// This is an undiscovered block. Map it to the current loop.
				innerLoopMap.put(src, loop);
				++numBlocks;

				if (src.equals(loop.getHeader()))
					continue;

				// Push all block's incoming edges on the back edge worklist.
				for (IREdge<?> incoming : cfg.getIncomingEdges(src))
					backEdgesWorkList.push(incoming);

			} else {
				// This is a discovered block. Find its outermost discovered loop.
				Loop subLoop = innerLoopMap.get(src); // inner most loop
				while (subLoop.getParent() != null)
					subLoop = subLoop.getParent();

				// If it is already discovered to be a subloop of this loop, continue.
				if (subLoop == loop)
					continue;

				// Discover a subloop of this loop.
				subLoop.setParent(loop);
				++numSubLoops;

				numBlocks += subLoop.getBlocks().size();
				IRBasicBlock subHeader = subLoop.getHeader();

				// Continue traversal along predecessors that are not loop-back edges
				// from
				// within this subloop tree itself. Note that a predecessor may directly
				// reach another subloop that is not yet discovered to be a subloop of
				// this loop, which we must traverse.
				// Push all block's incoming edges on the back edge deque.
				for (IREdge<?> incoming : cfg.getIncomingEdges(subHeader)) {
					IRBasicBlock preSubHeader = incoming.getSource();
					if (innerLoopMap.get(preSubHeader) != subLoop)
						backEdgesWorkList.push(incoming);
				}
			}
		}

		loop.setNumBlocks(numBlocks);
		loop.setNumSubLoops(numSubLoops);
	}

	/**
	 * Discover a subloop with the specified backedges such that: All blocks
	 * within this loop are mapped to this loop or a subloop. And all subloops
	 * within this loop have their parent loop set to this loop or a subloop.
	 */
	private static void discoverAndMapSubloopUnnatural(IRControlFlowGraph cfg,
	    Map<IRBasicBlock, Loop> innerLoopMap, Loop loop,
	    Iterable<? extends IREdge<? extends IRBasicBlock>> backEdges) {
		int numBlocks = 0, numSubLoops = 0;

		Deque<IREdge<?>> backEdgesWorkList = Queues.newArrayDeque();
		for (IREdge<?> backEdge : backEdges)
			backEdgesWorkList.push(backEdge);

		while (!backEdgesWorkList.isEmpty()) {
			IREdge<?> backEdge = backEdgesWorkList.pop();
			IRBasicBlock src = backEdge.getSource();

			if (!innerLoopMap.containsKey(src)) {
				// This is an undiscovered block. Map it to the current loop.
				innerLoopMap.put(src, loop);
				++numBlocks;

				if (src.equals(loop.getHeader()))
					continue;

				// Push all block's incoming edges on the back edge worklist.
				for (IREdge<?> incoming : cfg.getIncomingEdges(src))
					backEdgesWorkList.push(incoming);

			} else {
				// This is a discovered block. Find its outermost discovered loop.
				Loop subLoop = innerLoopMap.get(src); // inner most loop
				while (subLoop.getParent() != null)
					subLoop = subLoop.getParent();

				// If it is already discovered to be a subloop of this loop, continue.
				if (subLoop == loop)
					continue;

				// Discover a subloop of this loop.
				subLoop.setParent(loop);
				++numSubLoops;

				numBlocks += subLoop.getBlocks().size();
				IRBasicBlock subHeader = subLoop.getHeader();

				// Continue traversal along predecessors that are not loop-back edges
				// from
				// within this subloop tree itself. Note that a predecessor may directly
				// reach another subloop that is not yet discovered to be a subloop of
				// this loop, which we must traverse.
				// Push all block's incoming edges on the back edge deque.
				for (IREdge<?> incoming : cfg.getIncomingEdges(subHeader)) {
					IRBasicBlock preSubHeader = incoming.getSource();
					if (innerLoopMap.get(preSubHeader) != subLoop)
						backEdgesWorkList.push(incoming);
				}
			}
		}

		loop.setNumBlocks(numBlocks);
		loop.setNumSubLoops(numSubLoops);
	}

	private static Collection<IREdge<?>> detectBackEdge(Deque<IRBasicBlock> stack,
	    Set<IRBasicBlock> visited, IRControlFlowGraph cfg,
	    IRBasicBlock currBlock) {
		Collection<IREdge<?>> backEdges = Sets.newHashSet();
		if (visited.contains(currBlock))
			return backEdges;
		stack.push(currBlock);
		for (IREdge<?> out : cfg.getOutgoingEdges(currBlock)) {
			IRBasicBlock dest = out.getTarget();
			if (stack.contains(dest)) {
				backEdges.add(out);
			} else {
				Collection<IREdge<?>> resEdges = detectBackEdge(stack, visited, cfg,
				    dest);
				backEdges.addAll(resEdges);
			}
		}
		stack.pop();
		visited.add(currBlock);
		return backEdges;
	}

	private static Collection<IREdge<?>> detectBackEdges(IRControlFlowGraph cfg) {
		Deque<IRBasicBlock> stack = Queues.newArrayDeque();
		Set<IRBasicBlock> visited = Sets.newHashSet();
		return detectBackEdge(stack, visited, cfg, cfg.getEntry());
	}
}
