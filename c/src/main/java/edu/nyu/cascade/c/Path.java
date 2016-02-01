package edu.nyu.cascade.c;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ExecutionException;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IRLocation;
import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRStatement.StatementType;
import edu.nyu.cascade.util.CacheException;
import edu.nyu.cascade.util.IOUtils;
import edu.nyu.cascade.util.Identifiers;

final class Path implements Comparable<Path>{
  private final static LoadingCache<IRBasicBlock, Path> cache = CacheBuilder
      .newBuilder().build(new CacheLoader<IRBasicBlock, Path>(){
        public Path load(IRBasicBlock block) {
          return createForFreshBlock(block);
        }
      });
	
  private static String EDGE = "Edge";
  private static String ASSERT = "Assert";
  private static String FUNC = "Func";
  private static String LOOPENTRY = "LoopEntry";
  private static String LOOPENTER = "LoopEnter";
  private static String LOOPBACK = "LoopBack";
  private static String INVPRECOND = "InvPreCond";
  private static String INVPOSTCOND = "InvPostCond";
  private static String FUNCENT = "FuncEnt";
  private static String FUNCRET = "FuncRet";
  private static String LOOP = "Loop";
	
	private static BigInteger nextId = BigInteger.ZERO;
	
	private int iterTimes = 0;
	private final int size;
	private final BigInteger id;
  private final ImmutableList<IRStatement> statements;
  private final String asString;
  private final Collection<String> labels = Sets.newHashSet();
  private IRLocation startLoc, endLoc;
  
  static Path create(Collection<? extends IRStatement> stmts) {
  	Preconditions.checkNotNull(stmts);
  	Path path = new Path(stmts);
  	if(stmts.size() == 1 
  			&& stmts.iterator().next().getType().equals(StatementType.ASSERT))
  		path.labelAssert();
  	return path;
  }
  
  static Path create(Iterable<? extends IRStatement> stmts) {
	  return create(Lists.newArrayList(stmts));
	}
  
  static Path create(IRStatement stmt) {
	  return create(Collections.singletonList(stmt));
	}

	/**
	 * Return a path for <code>block</code>. For the same
	 * block, always return the same path.
	 * @param block
	 * @return
	 */
	static Path createForBlock(IRBasicBlock block) {
	  try {
	    Path path = cache.get(block);
	  	if(!block.getPreLabels().isEmpty())
	  		path.labels.addAll(block.getPreLabels());
	  	return path;
	  } catch (ExecutionException e) {
	    throw new CacheException(e);
	  }
	}
	
	static Path createForFreshBlock(IRBasicBlock srcBlock) {
		List<? extends IRStatement> stmts = srcBlock.getStatements();
		Path path = Path.create(stmts);
		path.startLoc = srcBlock.getStartLocation();
		path.endLoc = srcBlock.getEndLocation();
		path.labels.addAll(srcBlock.getPreLabels());
		
		switch(srcBlock.getType()) {
		case LOOP: {
			path.labelLoop();
			return path;
		}
		
		case FUNC_ENT: {
	  	if(stmts.size() == 1) {
	  		IRStatement stmt = stmts.get(0);
	  		if(stmt.getType().equals(StatementType.FUNC_ENT)) {
	  			path.labelFuncEnt();
		  	  return path;
	  		}
	  	}
		}
		case FUNC_EXIT: {
	  	if(stmts.size() == 1) {
	  		IRStatement stmt = stmts.get(0);
	  		if(stmt.getType().equals(StatementType.FUNC_EXIT)) {
	  			path.labelFuncRet();
	  			return path;
	  		}
	  	}
		}
		default: {
	  	if(stmts.size() == 1) {
	  		IRStatement stmt = stmts.get(0);
	  		if(stmt.hasProperty(Identifiers.STMTFUNCASSIGN) ||
	  				stmt.hasProperty(Identifiers.STMTFUNC)) {
	  			path.labelFuncPath();
	  			return path;
	  		}
	  		
	  		if(stmt.getType().equals(StatementType.ASSERT)) {
	  			path.labelAssert();
	  			return path;
	  		}
	  	}
	  	
	  	return path;
		}
		}
	}

	/**
	 * Merge <code>path1</code> and <code>path2</code> as path1 : path2
	 */
	static Path mergePath(Path path1, Path path2) {
	  Collection<IRStatement> mergeStmts = Lists.newArrayList(path1.getStmts());
	  mergeStmts.addAll(path2.getStmts());
	  return create(mergeStmts);
	}
	
	static void copyProperties(Path from, Path to) {
	  to.labels.addAll(from.labels);
	  to.iterTimes = from.iterTimes;
	}

	private Path(Collection<? extends IRStatement> stmts) {
		Preconditions.checkNotNull(stmts);
	  statements = ImmutableList.copyOf(stmts); 
	  id = nextId;
	  nextId = nextId.add(BigInteger.ONE);
	  size = stmts.size();
	  if(!stmts.isEmpty()) {
		  startLoc = statements.get(0).getLocation();
		  endLoc = statements.get(size-1).getLocation();
	  }
	  
	  StringBuilder sb = new StringBuilder();
		sb.append("Path ").append(id).append(": \n");
		for(int i = 0; i < statements.size(); i++) {
			IRStatement stmt = statements.get(i);
			sb.append(stmt.getLocation()).append(" ").append(stmt);
			if(i+1 < statements.size()) sb.append("\n");
		}
		
	  asString = sb.toString();
	}

	@Override
	public int compareTo(Path b) {
		return id.compareTo(b.id);
	}

	@Override
	public String toString() {
	  StringBuilder sb = new StringBuilder();
	  if(!labels.isEmpty()) {
	  	sb.append("(label: ").append(labels).append(")");
	  }
	  
	  if(startLoc != null && endLoc != null)	{
	  	sb.append("(").append(startLoc.getLine())
	  		.append(":").append(endLoc.getLine())
	  		.append(')');
	  }
	  
	  sb.append(asString);
	  return sb.toString();
	}

	@Override
	public Path clone() {
	  Path copy = Path.create(statements);
	  copy.startLoc = startLoc;
	  copy.endLoc = endLoc;
	  copy.labels.addAll(labels);
	  copy.iterTimes = iterTimes;
	  return copy;
	}

	Collection<IRStatement> getStmts() {
		return statements;
	}
	
	IRLocation getStartLoc() {
		return startLoc;
	}
	
	IRLocation getEndLoc() {
		return endLoc;
	}
  
  /**
   * Return <code>true</code> if path has no statements
   * @return
   */
  boolean isEmpty() {
    return statements.isEmpty();
  }
  
  boolean hasLabel() {
  	return !labels.isEmpty();
  }
  
  boolean isLoopPath() {
  	return labels.contains(LOOP);
  }
  
  boolean isEdgePath() {
  	return labels.contains(EDGE);
  }
  
  boolean isAssertPath() {
  	return labels.contains(ASSERT);
  }
  
  boolean isLoopEntry() {
  	return labels.contains(LOOPENTRY);
  }
  
  boolean isLoopEnter() {
  	return labels.contains(LOOPENTER);
  }
  
  boolean isLoopBack() {
  	return labels.contains(LOOPBACK);
  }
  
  boolean isFuncPath() {
  	return labels.contains(FUNC);
  }
  
  boolean isFuncEnt() {
  	return labels.contains(FUNCENT);
  }
  
  boolean isFuncRet() {
  	return labels.contains(FUNCRET);
  }
  
  boolean isInvPreCond() {
  	return labels.contains(INVPRECOND);
  }
  
  boolean isInvPostCond() {
  	return labels.contains(INVPOSTCOND);
  }
  
  void labelEdgePath() {
  	labels.add(EDGE);
  }
  
  void labelLoopEntry(int iterTimes) {
		labels.add(LOOPENTRY);
		this.iterTimes = iterTimes;
	}

  void labelLoopEnter() {
  	labels.add(LOOPENTER);
  }
  
  void labelLoopBack() {
  	labels.add(LOOPBACK);
  }
  
  void labelInvPreCond() {
  	labels.add(INVPRECOND);
  }
  
  void labelInvPostCond() {
  	labels.add(INVPOSTCOND);
  }
  
  boolean hasLabel(String label) {
	  return labels.contains(label);
  }
  
  int getSize() {
  	return size;
  }
  
  IRStatement getStmt(int index) {
  	Preconditions.checkElementIndex(index, size);
  	return statements.get(index);
  }
  
  int getIterTimes() {
  	return iterTimes;
  }
  
  String stmtsToString() {
	  StringBuilder sb = new StringBuilder();
	  sb.append(asString);
	  if(!labels.isEmpty()) {
	  	sb.append(" (label: ").append(labels).append(")");
	  }
		return sb.toString();
	}
	
  /** 
   * Split <code>path</code> into multiple paths, in order to filter out the path 
   * satisfies the <code>predicate</code>, and label it via <code>labelFunc</code>
   */ 
  List<Path> isolateKeyStatement(IRControlFlowGraph cfg,
  		Predicate<IRStatement> predicate) {
  	
  	/* The labels might be inv-pre and inv-post, which are no longer
  	 * useful. Ignore them and thus do not tag them to the sub-paths. 
  	 */
  	
  	if(hasLabel()) IOUtils.err().println("Isolated path has label: " + labels);
  	
  	List<IRStatement> stmts = Lists.newArrayList(statements);
  	List<Integer> indices = Lists.newArrayListWithExpectedSize(size);
  	
  	for(int i = 0; i < size; i++) {
  		if(predicate.apply(stmts.get(i))) indices.add(i);
  	}
  	
  	assert(!indices.isEmpty());
  	
  	int subPathSize = indices.size() * 2 + 1;
  	List<Path> subPaths = Lists.newArrayListWithExpectedSize(subPathSize);
  	
  	int preIndex = 0;
  	for(int index : indices) {
  		if(preIndex < index) { // add pre-path
  			Path tmpPath = Path.create(stmts.subList(preIndex, index));
  			subPaths.add(tmpPath);
  		}
  		
  		Path targetPath = Path.create(stmts.get(index));
  		subPaths.add(targetPath);  // add target path
  		preIndex = index+1;
  	}
  	
  	if(preIndex < size) {
  		Path lastPath = Path.create(stmts.subList(preIndex, size));
  		subPaths.add(lastPath); // add last-path
  	}
  	
  	return subPaths;
  }

	private void labelAssert() {
		labels.add(ASSERT);
	}

	private void labelLoop() {
		labels.add(LOOP);
	}

	private void labelFuncPath() {
		labels.add(FUNC);
	}

	private void labelFuncEnt() {
		labels.add(FUNCENT);
	}

	private void labelFuncRet() {
		labels.add(FUNCRET);
	}
}