package edu.nyu.cascade.ir.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;

public class DominatorTree {

	private final IRControlFlowGraph cfg;
	private final List<IRBasicBlock> blocks;
	private final Map<IRBasicBlock, Integer> blocksToIndex;
	private final List<Integer> i_dom;
	private final List<Collection<Integer>> dominated;
	
	private DominatorTree(IRControlFlowGraph cfg,
			List<IRBasicBlock> blocks,
			Map<IRBasicBlock, Integer> blocksToIndex,
			List<Integer> i_dom,
			List<Collection<Integer>> dominated) {
		this.cfg = cfg;
		this.blocks = blocks;
		this.blocksToIndex = blocksToIndex;
		this.i_dom = i_dom;
		this.dominated = dominated;
	}
	
	public static DominatorTree analyze(IRControlFlowGraph cfg) {
		Collection<IRBasicBlock> seq = ControlFlowGraph.topologicalSeq(cfg);
		int size = seq.size();
		List<IRBasicBlock> blocks = Lists.newArrayListWithExpectedSize(size);
		Map<IRBasicBlock, Integer> blocksToIndex = Maps.newHashMapWithExpectedSize(size);
		List<Integer> i_dom = Lists.newArrayListWithExpectedSize(size);
		List<Collection<Integer>> dominated = Lists.newArrayListWithExpectedSize(size);
		for(IRBasicBlock block : seq) { // reverse order
			blocks.add(0, block);
			blocksToIndex.put(block, blocks.size()-1);
			i_dom.add(-1);
			dominated.add(Collections.<Integer>emptyList());
		}
		computeDT(cfg, blocks, blocksToIndex, i_dom, dominated);
		return new DominatorTree(cfg, blocks, blocksToIndex, i_dom, dominated);
	}
	
	/**
	 * Get blocks in post-order
	 * @return
	 */
	public Collection<IRBasicBlock> getBlocks() {
		return blocks;
	}
	
	/** Does a particular block dominate another block? */
	public boolean dominates(IRBasicBlock block, IRBasicBlock potentialSucc) {
		int id = blocksToIndex.get(block);
		int successorId = blocksToIndex.get(potentialSucc);
		int startId = blocksToIndex.get(cfg.getEntry());
		
		boolean dominates = false;
		
		int nextId = successorId;
		
		do
		{
			dominates = nextId == id;
			nextId = i_dom.get(nextId);
		} while(startId != nextId && !dominates);
		
		return dominates || nextId == id;
	}
	
	/** Get the dominator of a given block */
	public IRBasicBlock getDominator(IRBasicBlock block) {
		return blocks.get(i_dom.get(blocksToIndex.get(block)));
	}
	
	/** Get the nearest common dominator of two blocks */
	public IRBasicBlock getCommonDominator(IRBasicBlock block1, IRBasicBlock block2) {
		int n1 = blocksToIndex.get(block1);
		int n2 = blocksToIndex.get(block2);
		
		int n = intersect(i_dom, i_dom.get(n1), i_dom.get(n2));
		
		return blocks.get(n);
	}
	
	/** Get the set of blocks immediately dominated by the specified block */
	public Collection<IRBasicBlock> getDominatedBlocks(IRBasicBlock block) {
		int idx = blocksToIndex.get(block);
		Collection<IRBasicBlock> resBlocks = Lists.newArrayListWithCapacity(
				dominated.get(idx).size());
		for(int domIdx : dominated.get(idx)) resBlocks.add(blocks.get(domIdx));
		return resBlocks;
	}
	
	/** Computes the dominator tree from a CFG using algorithm described in
	 * "A simple and fast dominance algorithm" by 
	 *			Keith D. Cooper, Timothy J. Harvey, and Ken Kennedy
	 */
	private static void computeDT(IRControlFlowGraph cfg, 
			List<IRBasicBlock> blocks, 
			Map<IRBasicBlock, Integer> blocksToIndex, 
			List<Integer> i_dom,
			List<Collection<Integer>> dominated) {
		IRBasicBlock entry = cfg.getEntry();
		int startIdx = blocksToIndex.get(entry);
		
		boolean changed = true;
		i_dom.set(startIdx, startIdx);
		
		while(changed) {
			changed = false;
			
			//reverse post-order
			for(IRBasicBlock currBlock : blocks) {
				if(currBlock.equals(entry)) continue;
				int new_idom = 0;
				boolean processed = false;
				for(IREdge<?> incoming : cfg.getIncomingEdges(currBlock)) {
					IRBasicBlock src = incoming.getSource();
					int srcIdx = blocksToIndex.get(src);
					if(i_dom.get(srcIdx) == -1) continue;
					
					if(processed) {
						new_idom = intersect(i_dom, srcIdx, new_idom);
					} else {
						processed = true;
						new_idom = srcIdx;
					}
				}
				
				if(processed) {
					int currIdx = blocksToIndex.get(currBlock);
					if(i_dom.get(currIdx) != new_idom) {
						i_dom.set(currIdx, new_idom);
						changed = true;
					}
				}
			}
		}
		
		for(int n = 0; n < blocks.size(); n++) {
			int i_dom_n = i_dom.get(n);
			if(i_dom_n >= 0) {
				Collection<Integer> doms = dominated.get(i_dom_n);
				if(doms.isEmpty()) {
					doms = Sets.newHashSet(n);
					dominated.set(i_dom_n, doms);
				} else {
					doms.add(n);
				}
			}
		}
	}
	
	private static int intersect(List<Integer> i_dom, int b1, int b2) {
		int finger1 = b1;
		int finger2 = b2;
		while (finger1 != finger2) {
			while (finger1 < finger2) {
				finger1 = i_dom.get(finger1);
			}
			while (finger2 < finger1) {
				finger2 = i_dom.get(finger2);
			}
		}
		return finger1;
	}
}
