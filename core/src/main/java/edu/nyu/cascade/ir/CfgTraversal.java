package edu.nyu.cascade.ir;

import java.util.LinkedList;
import java.util.TreeSet;


/** A CFG traversal strategy. */
public final class CfgTraversal {
  public static interface BlockVisitor {
    void visit(IRBasicBlock block);
  }

  public static void visitBlocks(IRControlFlowGraph cfg, BlockVisitor visitor) {
    // hit all reachable BBs (though not necessarily in top
    // order), ensuring we don't hit the same one twice
    LinkedList<IRBasicBlock> worklist = new LinkedList<IRBasicBlock>();
    TreeSet<IRBasicBlock> seen = new TreeSet<IRBasicBlock>();
    worklist.add(cfg.getEntry());

    while (!worklist.isEmpty()) {
      IRBasicBlock blk = worklist.remove();
      if (!seen.contains(blk)) {
        visitor.visit(blk);
        seen.add(blk);
        worklist.addAll(cfg.getSuccessors(blk));
      }
    }
  }
}