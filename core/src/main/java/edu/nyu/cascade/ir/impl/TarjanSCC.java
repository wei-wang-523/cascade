package edu.nyu.cascade.ir.impl;

import java.util.Deque;
import java.util.List;
import java.util.Map;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Queues;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;

class TarjanSCC {
	private boolean[] marked; // marked[v] = has v been visited?
	private int[] id;                // id[v] = id of strong component containing v
  private int[] low;               // low[v] = low number of v
  private int pre;                 // preorder number counter
  private int count;               // number of strongly-connected components
  private Deque<Integer> stack;
  private Map<IRBasicBlock, Integer> blocksToIndex;
  private List<IRBasicBlock> blocks;
  
  /**
   * Computes the strong components of the digraph <tt>G</tt>.
   * @param G the digraph
   */
  public TarjanSCC(IRControlFlowGraph cfg) {
  	int size = cfg.getBlocks().size();
  	
  	blocks = Lists.newArrayListWithCapacity(size);
  	blocksToIndex = Maps.newHashMapWithExpectedSize(size);
  	int i = 0;
  	for(IRBasicBlock block : cfg.topologicalSeq(cfg.getEntry())) {
			blocks.add(0, block);
			blocksToIndex.put(block, size - (++i));
  	}
  	
  	marked = new boolean[size];
  	stack = Queues.newArrayDeque();
    id = new int[size]; 
    low = new int[size];
    dfs(cfg, cfg.getEntry());
  }

  private void dfs(IRControlFlowGraph cfg, IRBasicBlock block) {
  	int srcIdx = blocksToIndex.get(block);
  	marked[srcIdx] = true;
  	low[srcIdx] = pre++;
  	int min = low[srcIdx];
  	stack.push(srcIdx);
  	for(IREdge<?> outgoing : cfg.getOutgoingEdges(block)) {
  		IRBasicBlock dest = outgoing.getTarget();
  		int destIdx = blocksToIndex.get(outgoing.getTarget());
  		if(!marked[destIdx]) dfs(cfg, dest);
  		if (low[destIdx] < min)  min = low[destIdx];
  	}
  	
  	if (min < low[srcIdx]) { 
  		low[srcIdx] = min; return; 
  	}
  	
  	int w;
  	do {
  		w = stack.pop();
  		id[w] = count;
  		low[w] = blocksToIndex.size()-1;
  	} while (w != srcIdx);
  	
  	count++;
  }
}
