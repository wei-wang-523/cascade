package edu.nyu.cascade.c;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import xtc.tree.GNode;
import xtc.tree.Node;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRStatement.StatementType;
import edu.nyu.cascade.ir.impl.BasicBlock;
import edu.nyu.cascade.ir.impl.IRExpressionImpl;
import edu.nyu.cascade.ir.impl.Loop;
import edu.nyu.cascade.ir.impl.LoopInfoUtil;
import edu.nyu.cascade.ir.impl.Statement;
import edu.nyu.cascade.util.IOUtils;

public class CfgProcessor {
	
	/**
	 * Append <code>preCFG</code> to <code>mainCFG</code>, have side-effect on <code>
	 * mainCFG</code>
	 * 
	 * @param preCFG
	 * @param mainCFG
	 */
	public static void appendPreCFG(IRControlFlowGraph preCFG, IRControlFlowGraph mainCFG) {
		for(IRBasicBlock preBlock : preCFG.getBlocks()) {
			for(IREdge<? extends IRBasicBlock> edge : preCFG.getIncomingEdges(preBlock)) 
				mainCFG.addEdge(edge);
		}
		
		IRBasicBlock preExit = preCFG.getExit();
		IRBasicBlock mainEntry = mainCFG.getEntry();
		if(preExit != mainEntry) mainCFG.addEdge(preExit, mainEntry);
		mainCFG.setEntry(preCFG.getEntry());
		mainCFG.format(IOUtils.debug());
	}
	
	public static void insertParamArgAssignStmts(IRControlFlowGraph funcCfg, 
			Collection<IRStatement> assignStmts) {
		IRBasicBlock entry = funcCfg.getEntry();
		IRBasicBlock currBlock = entry;
		
		while(currBlock.getStatements().isEmpty()) {
			Collection<? extends IRBasicBlock> succs = funcCfg.getSuccessors(currBlock);
			assert(succs.size() == 1);
			currBlock = succs.iterator().next();
		}
		
		List<IRStatement> newStmts = Lists.newArrayList();
		Iterator<IRStatement> itr = assignStmts.iterator();
		for(IRStatement stmt : currBlock.getStatements()) {
			newStmts.add(stmt);
			if(StatementType.DECLARE.equals(stmt.getType())) {
				if(itr.hasNext()) newStmts.add(itr.next());
			}
		}
		IRBasicBlock newBlock = BasicBlock.create();
		newBlock.addStatements(newStmts);
		newBlock.setScope(currBlock.getScope());
		//FIXME: ignore the labels of paramDeclareBlock;
	
		replaceBlock(funcCfg, currBlock, newBlock);
	}
	
	public static void appendReturnStmt(IRControlFlowGraph funcCfg, IRStatement assignStmt) {
	  Preconditions.checkArgument(assignStmt.getType().equals(StatementType.ASSIGN));

	  for(IRBasicBlock block : funcCfg.getBlocks()) {
	  	if(block.getStatements().isEmpty()) continue;
	  	int lastIdx = block.getStatements().size()-1;
	  	IRStatement lastStmt = block.getStatements().get(lastIdx);
	  	if(!StatementType.RETURN.equals(lastStmt.getType())) continue;
	  	if(lastStmt.getOperands().size() == 0) continue; // no operand
	  	IRStatement retAsgn = createReturnAssignStmt(lastStmt, assignStmt);
	  	block.addStatement(retAsgn);
	  }
	}
	
	public static boolean simplifyCFG(IRControlFlowGraph cfg) {
		boolean EverChanged = false;
		EverChanged |= deleteDeadBlocks(cfg);
		
		boolean merged = false;
		boolean localChanged = true;
		
		while(localChanged) {
			localChanged = false;
			for(IRBasicBlock block : cfg.topologicalSeq(cfg.getEntry())) {
				localChanged |= mergeBlockIntoPredecessor(cfg, block);
			}
			merged |= localChanged;
		}
		
		if(merged) {
			IOUtils.debug().p("After merge blocks: ");
			IOUtils.debug().incr();
			cfg.format(IOUtils.debug());
			IOUtils.debug().decr();
		}
		
		EverChanged |= merged;
		return EverChanged;
	}
	
	public static boolean simplifyCFG(IRControlFlowGraph cfg, String label) {
		boolean EverChanged = false;
		EverChanged |= deleteDeadBlocks(cfg);
		
		boolean merged = false;
		boolean localChanged = true;
		
		while(localChanged) {
			localChanged = false;
			for(IRBasicBlock block : cfg.topologicalSeq(cfg.getEntry())) {
				if(block.getPreLabels().contains(label)) continue;
				localChanged |= mergeBlockIntoPredecessor(cfg, block);
			}
			merged |= localChanged;
		}
		
		if(merged) {
			IOUtils.debug().p("After merge blocks: ");
			IOUtils.debug().incr();
			cfg.format(IOUtils.debug());
			IOUtils.debug().decr();
		}
		
		EverChanged |= merged;
		return EverChanged;
	}
	
	public static void havocLoop(IRControlFlowGraph cfg, 
			IRBasicBlock loopHeader, 
			IRStatement preLoopAssertion, 
			IRStatement postLoopAssumption) {
		Preconditions.checkArgument(cfg.getEntry() == cfg.getExit());
		
		Loop loop = LoopInfoUtil.getLoop(cfg, loopHeader);
		
		IRBasicBlock postLoopBlock = BasicBlock.create();
		postLoopBlock.addStatements(Collections.singletonList(postLoopAssumption));
		
		IRBasicBlock preLoopBlock = BasicBlock.create();
		List<IRStatement> preLoopStmts = Lists.newArrayList(preLoopAssertion);
		preLoopBlock.addStatements(preLoopStmts);
		
		List<IRStatement> liftHavocDeclStmts = liftHavocDeclStatements(loop);
		preLoopBlock.addStatements(liftHavocDeclStmts);
		
		Collection<IREdge<?>> backEdges = loop.getBackEdges();
		Collection<IREdge<?>> enterEdges = Lists.newArrayList(cfg.getIncomingEdges(loopHeader));
		enterEdges.removeAll(backEdges);
		
		for(IREdge<?> enterEdge : enterEdges) {
			IRBasicBlock preLoopHeader = enterEdge.getSource();
			cfg.addEdge(preLoopHeader, enterEdge.getGuard(), preLoopBlock);
			cfg.removeEdge(enterEdge);
		}
		
		cfg.addEdge(preLoopBlock, loopHeader);
		
		for(IREdge<?> backEdge : backEdges) {
			IRBasicBlock src = backEdge.getSource();
			cfg.addEdge(src, backEdge.getGuard(), postLoopBlock);
			cfg.removeEdge(backEdge);
		}
		
		for(IREdge<?> outEdge : cfg.getOutgoingEdges(loopHeader)) {
			IRBasicBlock dest = outEdge.getTarget();
			if(loop.containsBlock(dest)) continue;
			// loop exit edges from loop header
			cfg.addEdge(postLoopBlock, outEdge.getGuard(), dest);
			cfg.removeEdge(outEdge);
		}
	}
	
	private static void replaceBlock(IRControlFlowGraph cfg, 
			IRBasicBlock oldBlock, 
			IRBasicBlock newBlock) {
	
		Collection<? extends IREdge<? extends IRBasicBlock>> incomings 
				= ImmutableList.copyOf(cfg.getIncomingEdges(oldBlock));
		
		for(IREdge<?> edge : incomings) {
			cfg.addEdge(edge.getSource(), edge.getGuard(), newBlock);
			cfg.removeEdge(edge);
		}
		
		Collection<? extends IREdge<? extends IRBasicBlock>> outgoings
				= ImmutableList.copyOf(cfg.getOutgoingEdges(oldBlock));
		
		for(IREdge<?> edge : outgoings) {
			cfg.addEdge(newBlock, edge.getGuard(), edge.getTarget());
			cfg.removeEdge(edge);
		}
		
		if(oldBlock == cfg.getEntry())		cfg.setEntry(newBlock);
		if(oldBlock == cfg.getExit())	  cfg.setExit(newBlock);
	}
	
	/**
	 * Merge basic blocks into their predecessor if there is only one distinct 
	 * predecessor, and it there is only one distinct successor of the predecessor
	 * 
	 * @param cfg
	 */
	private static boolean mergeBlockIntoPredecessor(IRControlFlowGraph cfg, IRBasicBlock block) {
		Collection<? extends IRBasicBlock> predBBs = cfg.getPredecessors(block);
		/* No merge with multiple predecessors, or no predecessors */
		if(predBBs.size() != 1) return false;
		
		IRBasicBlock predBB = predBBs.iterator().next();
		
		/* Do not break self-loops */
		if(predBB == block) return false;
		
		/* Do not merge if predBB's last statement is a terminator */
		List<? extends IRStatement> predBBStmts = predBB.getStatements();
		if(!predBBStmts.isEmpty()) {
			IRStatement lastStmt = predBBStmts.get(predBBStmts.size() - 1);
			if(StatementType.RETURN.equals(lastStmt.getType())) return false;
		}
		
		/* Traverse successors of the single predecessor, check if all of them 
		 * are same of this block. Cannot merge if there are multiple successors.
		 */
		IRBasicBlock uniqueSucc = block;
		for(IRBasicBlock predBBSucc : cfg.getSuccessors(predBB)) {
			if(predBBSucc != block) {
				uniqueSucc = null; break;
			}
		}
		
		if(uniqueSucc == null) return false;
		
		/* Get rid of unneeded guarded incoming edge (guard as the 
		 * last assumption statement of predBB).
		 */
		Collection<? extends IREdge<? extends IRBasicBlock>> incomings = cfg.getIncomingEdges(uniqueSucc);
		assert(incomings.size() == 1);
		IREdge<?> incoming = incomings.iterator().next();
		if(incoming.getGuard() != null) {
			IRStatement assumeStmt = Statement.assumeStmt(incoming.getSourceNode(), incoming.getGuard());
			predBB.addStatement(assumeStmt);
		}
		
		/* Replace all use with BB with PredBB */
		Collection<IREdge<?>> outgoings = ImmutableList.copyOf(cfg.getOutgoingEdges(uniqueSucc));
		for(IREdge<?> outgoing : outgoings) {
			IRBasicBlock dest = outgoing.getTarget();
			cfg.removeEdge(outgoing);
			cfg.addEdge(predBB, outgoing.getGuard(), dest);
		}
		
		/* Replace the cfg exit to predBB if BB is the exit */
		if(cfg.getExit() == uniqueSucc) cfg.setExit(predBB);
		
		/* Move all the instructions in the BB to PredBB */
		predBB.addStatements(uniqueSucc.getStatements());
		
		/* Finally, erase the old block */
		cfg.removeBlock(uniqueSucc);
		
		return true;
	}

	private static boolean deleteDeadBlocks(IRControlFlowGraph cfg) {
		Collection<IRBasicBlock> topologicSeq = cfg.topologicalSeq(cfg.getEntry());
		Collection<IRBasicBlock> deadBlocks = Lists.newArrayList(cfg.getBlocks());
		deadBlocks.removeAll(topologicSeq); // remained are dead blocks;
		if(deadBlocks.isEmpty()) return false;
		
		for(IRBasicBlock block : deadBlocks) cfg.removeBlock(block);
		return true;
	}
	
	private static List<IRStatement> liftHavocDeclStatements(Loop loop) {
		List<IRStatement> liftStmts = Lists.newArrayList();
		
		/* Avoid to have multiple havoc statements for same left-variable */
		Set<GNode> havocGNodeSet = Sets.newHashSet();
		
		// Use the reverse of post-order
		List<IRBasicBlock> blocks = Lists.reverse(ImmutableList.copyOf(loop.getBlocks()));
		for(IRBasicBlock block : blocks) { 
			for(IRStatement stmt : block.getStatements()) {
				switch(stmt.getType()) {
				case MALLOC:
				case ASSIGN:
					/* Pick up havoc statements for any update */
					Statement havocStmt = Statement.havoc(stmt.getSourceNode(), stmt.getOperand(0));
					GNode havocGNode = GNode.cast(stmt.getOperand(0).getSourceNode());
					if(havocGNodeSet.contains(havocGNode)) continue;
					
					havocGNodeSet.add(havocGNode);
					liftStmts.add(havocStmt);
					break;
				case HAVOC:
				case DECLARE:
					liftStmts.add(stmt); break;
				default:
					break;
			}
			}
		}
		
		return liftStmts;
	}
	
	/**
	 * Replace the <code>returnStmt</code> as <code>assignStmt</code>
	 * @param returnStmt
	 * @param assignStmt
	 * @return
	 */
  private static IRStatement createReturnAssignStmt(
  		IRStatement returnStmt, 
  		IRStatement assignStmt) {
    Preconditions.checkArgument(StatementType.RETURN.equals(returnStmt.getType()));
    Preconditions.checkArgument(StatementType.ASSIGN.equals(assignStmt.getType()));
    IRExpressionImpl lExpr = (IRExpressionImpl) assignStmt.getOperand(0);
    IRExpressionImpl rExpr = (IRExpressionImpl) returnStmt.getOperand(0);
    Node assignNode = GNode.create("AssignmentExpression", 
        lExpr.getSourceNode(), "=", rExpr.getSourceNode());
    assignNode.setLocation(assignStmt.getSourceNode().getLocation());
    IRStatement assignResult = Statement.assign(assignNode, lExpr, rExpr);
    return assignResult;
  }
}
