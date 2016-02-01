package edu.nyu.cascade.ir.impl;

import java.util.Collection;
import java.util.Deque;
import java.util.List;

import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Queues;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;

public class Loop {
	private final IRControlFlowGraph cfg;
	private final IRBasicBlock loopHeader;
	private final List<IRBasicBlock> blocks;
	private Collection<IREdge<? extends IRBasicBlock>> backEdges, exitEdges;
	private Collection<IRBasicBlock> blocksInExitRound, blocksInLoopRound;
	private int numBlocks;
	private int numSubLoops;
	private List<Loop> subLoops = Lists.newArrayList();
	private Loop parent = null;
	private int unrollTime = 0;
	
	public Loop(IRControlFlowGraph cfg, IRBasicBlock loopHeader) {
		this.cfg = cfg;
		this.loopHeader = loopHeader;
		this.blocks = Lists.newArrayList(loopHeader);
	}

	public IRBasicBlock getHeader() {
	  return loopHeader;
  }

	public Loop getParent() {
	  return parent;
  }
	
	public void setParent(Loop parent) {
		this.parent = parent;
	}
	
	public boolean addSubLoop(Loop subLoop) {
		return subLoops.add(subLoop);
	}
	
	public Collection<IRBasicBlock> getBlocks() {
	  return blocks;
  }
	
	public boolean containsBlock(IRBasicBlock block) {
		return blocks.contains(block);
	}
	
	public boolean addBlock(IRBasicBlock block) {
		return blocks.add(block);
	}
	
	public void setNumBlocks(int numBlocks) {
		this.numBlocks = numBlocks;
	}
	
	public void setNumSubLoops(int numSubLoops) {
		this.numSubLoops = numSubLoops;
	}
	
	public int getNumBlocks() {
		return numBlocks;
	}
	
	public Collection<Loop> getSubLoops() {
		return subLoops;
	}
	
	public int getNumSubLoops() {
		return numSubLoops;
	}
	
	public Collection<IREdge<? extends IRBasicBlock>> getBackEdges() {
		if(backEdges == null) {
			backEdges = Lists.newArrayList(
					Iterables.filter(cfg.getIncomingEdges(loopHeader), 
							new Predicate<IREdge<?>>() {
						@Override
						public boolean apply(IREdge<?> incomingEdge) {
							return blocks.contains(incomingEdge.getSource());
						}
			}));
		}
		return backEdges;
	}
	
	public Collection<IREdge<? extends IRBasicBlock>> getExitEdges() {
		if(exitEdges == null) {
			exitEdges = Lists.newArrayList();
			for(IRBasicBlock block : blocks) {
				for(IREdge<? extends IRBasicBlock> outgoing : cfg.getOutgoingEdges(block)) {
					IRBasicBlock dest = outgoing.getTarget();
					if(blocks.contains(dest)) continue;
					exitEdges.add(outgoing);
				}
			}
		}
		return exitEdges;
	}
	
	public int getUnrollTime() {
		return unrollTime;
	}
	
	public void setUnrollTime(int unrollTime) {
		this.unrollTime = unrollTime;
	}
	
	public Collection<IRBasicBlock> getBlocksInExitRound() {
		if(blocksInExitRound != null) return blocksInExitRound;
		Collection<IRBasicBlock> resBlockSet = Sets.newHashSet(loopHeader);
		Deque<IRBasicBlock> stack = Queues.newArrayDeque();
		for(IREdge<? extends IRBasicBlock> exitEdge : getExitEdges()) {
			IRBasicBlock src = exitEdge.getSource();
			stack.add(src);
		}
		
		while(!stack.isEmpty()) {
			IRBasicBlock block = stack.pop();
			if(!resBlockSet.add(block)) continue;
			for(IRBasicBlock predBB : cfg.getPredecessors(block)) {
				if(blocks.contains(predBB)) stack.add(predBB);
			}
		}
		
		blocksInExitRound = resBlockSet;
		return blocksInExitRound;
	}
	
	public Collection<IRBasicBlock> getBlocksInLoopRound() {
		if(blocksInLoopRound != null) return blocksInLoopRound;
		Collection<IRBasicBlock> resBlockSet = Sets.newHashSet(loopHeader);
		Deque<IRBasicBlock> stack = Queues.newArrayDeque();
		for(IREdge<? extends IRBasicBlock> exitEdge : getBackEdges()) {
			IRBasicBlock src = exitEdge.getSource();
			stack.add(src);
		}
		
		while(!stack.isEmpty()) {
			IRBasicBlock block = stack.pop();
			if(!resBlockSet.add(block)) continue;
			for(IRBasicBlock predBB : cfg.getPredecessors(block)) {
				if(blocks.contains(predBB)) stack.add(predBB);
			}
		}
		
		blocksInLoopRound = resBlockSet;
		return blocksInLoopRound;
	}
}
