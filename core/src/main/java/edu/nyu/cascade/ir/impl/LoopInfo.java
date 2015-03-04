package edu.nyu.cascade.ir.impl;

import java.util.Collection;
import java.util.Map;

import edu.nyu.cascade.ir.IRBasicBlock;

public class LoopInfo {
	// Mapping of basic blocks to the inner most loop they occur in
	private final Map<IRBasicBlock, Loop> innerLoopMap;
	// All the top-level tops without parent loop
	private final Collection<Loop> topLevelLoops;
	
	LoopInfo(Map<IRBasicBlock, Loop> innerLoopMap, Collection<Loop> topLevelLoops) {
		this.innerLoopMap = innerLoopMap;
		this.topLevelLoops = topLevelLoops;
	}
	
	public Map<IRBasicBlock, Loop> getInnerLoopMap() {
	  return innerLoopMap;
	}

	public Collection<Loop> getTopLevelLoops() {
	  return topLevelLoops;
	}
}
