package edu.nyu.cascade.ir.impl;

import java.util.Collection;
import java.util.List;

import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;

public class Loop {
	private final IRControlFlowGraph cfg;
	private final IRBasicBlock loopHeader;
	private final List<IRBasicBlock> blocks;
	private Collection<IREdge<?>> backEdges, exitEdges;
	private int numBlocks;
	private int numSubLoops;
	private List<Loop> subLoops = Lists.newArrayList();
	private Loop parent = null;
	
	public Loop(IRControlFlowGraph cfg, IRBasicBlock loopHeader) {
		this.cfg = cfg;
		this.loopHeader = loopHeader;
		this.blocks = Lists.newArrayList();
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
	
	public int getNumSubLoops() {
		return numSubLoops;
	}
	
	public Collection<IREdge<?>> getBackEdges() {
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
	
	public Collection<IREdge<?>> getExitEdges() {
		if(exitEdges == null) {
			exitEdges = Lists.newArrayList();
			for(IRBasicBlock block : blocks) {
				for(IREdge<?> outgoing : cfg.getOutgoingEdges(block)) {
					IRBasicBlock dest = outgoing.getTarget();
					if(blocks.contains(dest)) continue;
					exitEdges.add(outgoing);
				}
			}
		}
		return exitEdges;
	}
}
