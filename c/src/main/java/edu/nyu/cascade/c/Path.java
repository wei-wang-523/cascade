package edu.nyu.cascade.c;

import java.util.List;
import java.util.Stack;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.prover.Expression;

final class Path {
  private final IRBasicBlock srcBlock;
  private final List<IRStatement> stmts;
  private final IRBasicBlock destBlock;
  private Stack<Expression> guards = null;
  
  static Path createSingleton(List<? extends IRStatement> stmts) {
    if(stmts == null || stmts.isEmpty()) return null;
    return create(stmts, null, null);
  }
  
  IRBasicBlock getSrcBlock() {
		return srcBlock;
	}

	List<IRStatement> getStmts() {
		return stmts;
	}

	IRBasicBlock getDestBlock() {
		return destBlock;
	}

	Stack<Expression> getGuards() {
		return guards;
	}

	static Path createSingleton(IRStatement stmt) {
    List<IRStatement> stmts = Lists.newArrayList(stmt);
    return create(stmts, null, null);
  }
  
  static Path create(List<? extends IRStatement> stmts, IRBasicBlock srcBlock, 
      IRBasicBlock destBlock) {
    return new Path(stmts, srcBlock, destBlock);
  }
  
  static Path createWithBlock(IRBasicBlock block) {
  	return create(block.getStatements(), block, block);
  }
  
  private Path(List<? extends IRStatement> stmts, IRBasicBlock srcBlock, IRBasicBlock destBlock) {
    this.destBlock = destBlock;
    this.srcBlock = srcBlock;
    this.stmts = Lists.newArrayList(stmts);
  }
  
  void addGuard(Expression guard) {
    Preconditions.checkArgument(guard.isBoolean());
    if(guards == null)  guards = new Stack<Expression>();
    guards.push(guard);
  }
  
  void setGuards(Stack<Expression> guards) {
    Preconditions.checkArgument(this.guards == null);
    this.guards = guards;
  }
  
  boolean hasGuard() {
    return guards != null && !guards.isEmpty();
  }
  
  boolean isEmpty() {
    return stmts.isEmpty();
  }
  
  boolean hasBlocks() {
    return srcBlock != null || destBlock != null;
  }
  
  IRStatement getStmt(int index) {
    Preconditions.checkArgument(index >= 0 && index < stmts.size());
    return stmts.get(index);
  }
  
  IRStatement getLastStmt() {
    Preconditions.checkArgument(stmts != null && !stmts.isEmpty());
    return stmts.get(stmts.size()-1);
  }
  
  boolean replaceStmt(int index, IRStatement stmt) {
    Preconditions.checkArgument(index >= 0 && index < stmts.size());
    stmts.remove(index);
    stmts.add(index, stmt);
    return true;
  }
  
  IRBasicBlock getBlock(int index) {
    Preconditions.checkArgument(index >= 0 && index <= stmts.size());
    if(!hasBlocks())    return null;    
    if(index == 0)      return srcBlock;
    
    IRLocation pos = stmts.get(index).getLocation();
    if(srcBlock != null && pos.isWithin(srcBlock))      return srcBlock;
    if(destBlock != null && pos.isWithin(destBlock))    return destBlock;
    return getBlock(index-1);
  }
  
  List<Path> split(int index) {
    Preconditions.checkArgument(index >= 0 && index <= stmts.size());
    List<Path> resPaths = Lists.newArrayList();
    IRBasicBlock splitBlock = null;
    if(index == 0) {
      resPaths.add(null);
      resPaths.add(this);
    } else if(index == stmts.size()){
      resPaths.add(this);
      resPaths.add(null);
    } else {
      splitBlock = getBlock(index);
      Path path_1 = Path.create(stmts.subList(0, index), srcBlock, splitBlock);
      Path path_2 = Path.create(stmts.subList(index, stmts.size()), splitBlock, destBlock);
      resPaths.add(path_1);
      resPaths.add(path_2);
    }
    return resPaths;
  }
  
  static Path mergePath(Path path1, Path path2) {
    IRBasicBlock srcBlockPrime = path1.srcBlock;
    IRBasicBlock destBlockPrime = path2.destBlock;
    List<IRStatement> stmtsPrime = Lists.newArrayList(path1.stmts);
    stmtsPrime.addAll(path2.stmts);
    Path resPath = Path.create(stmtsPrime, srcBlockPrime, destBlockPrime);
    return resPath;
  }
  
  @Override
  public String toString() {
    String srcId = srcBlock == null ? "null" : srcBlock.getId().toString();
    String destId = destBlock == null ? "null" : destBlock.getId().toString();
    StringBuilder sb = new StringBuilder().append('(').append(srcId)
        .append(": ").append(destId).append(')').append(stmts);
    return sb.toString();
  }
  
  boolean isCopyOf(Object other) {
    if(other == null)   return false;
    if(!(other instanceof Path)) return false;
    if(other == this) return true;
    Path otherPath = (Path) other;
    return srcBlock.equals(otherPath.srcBlock) && 
      destBlock.equals(otherPath.destBlock) && 
      stmts.equals(otherPath.stmts);
  }
}