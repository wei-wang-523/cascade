package edu.nyu.cascade.ir.impl;

import java.util.Map;

import xtc.tree.Printer;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRTraceNode;
import edu.nyu.cascade.prover.ExpressionManager;

public class TraceFactory {
	private Map<IRBasicBlock, IRTraceNode> blockCache = Maps.newHashMap();
	private Map<IREdge<?>, IRTraceNode> edgeCache = Maps.newHashMap();
	
	public TraceFactory() {}
	
	public void reset() {
		blockCache.clear(); edgeCache.clear();
	}
	
	public IRTraceNode create(IRBasicBlock block) {
		TraceNode node = new TraceNode(false);
		blockCache.put(block, node); // update block cache
		return node;
	}
	
	public IRTraceNode create(IREdge<?> edge) {
		TraceNode node = new TraceNode(true);
		edgeCache.put(edge, node); // update block cache
		return node;
	}
	
	public boolean hasEncodeEdge(IREdge<?> edge) {
		return edgeCache.containsKey(edge);
	}
	
	public void eraseEncodeEdge(IREdge<?> edge) {
		edgeCache.remove(edge);
	}
	
	public IRTraceNode getTraceNode(IRBasicBlock block) {
		Preconditions.checkArgument(blockCache.containsKey(block));
		return blockCache.get(block);
	}
	
	public IRTraceNode getTraceNode(IREdge<?> edge) {
		Preconditions.checkArgument(edgeCache.containsKey(edge));
		return edgeCache.get(edge);
	}

	public void dumpTrace(IRTraceNode entry, Printer printer) {
		printer.pln()
		.pln("Trace :")
		.incr();
	  
	  entry.format(printer);
	  
	  printer.decr().pln();
	  printer.flush();
	}

	public void filterCounterExample(ExpressionManager exprManager, IRTraceNode entry) {
		entry.filterSuccessor(exprManager);
	}
}
