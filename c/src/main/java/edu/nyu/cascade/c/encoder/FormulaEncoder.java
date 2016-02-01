package edu.nyu.cascade.c.encoder;

import java.util.Collection;

import edu.nyu.cascade.c.SafeResult;
import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.IRBasicBlock;
import edu.nyu.cascade.ir.IRControlFlowGraph;
import edu.nyu.cascade.ir.IREdge;
import edu.nyu.cascade.ir.IRTraceNode;
import edu.nyu.cascade.ir.impl.LoopInfo;
import edu.nyu.cascade.ir.impl.TraceFactory;
import edu.nyu.cascade.ir.path.PathFactoryException;
import edu.nyu.cascade.ir.state.StateExpression;
import edu.nyu.cascade.util.Pair;

public interface FormulaEncoder {
  
	interface BlockEncodingStrategy<T> {
		Pair<Boolean, T> apply(IRBasicBlock block, T preState) 
    		throws PathFactoryException;
  }
	
	interface EdgeEncodingStrategy<T> {
		Pair<Boolean, T> apply(IREdge<?> edge, T preState) 
				throws PathFactoryException;
	}
	
	interface PhiNodeResolveStrategy<T> {
		T apply(Collection<T> preStates);
	}
	
	interface TraceEncodeStrategy {
		void encode(IREdge<?> edge);
		void encode(IRBasicBlock block);
	}
	
	interface MemLeakCheckStrategy<T> {
		void apply(T state) throws PathFactoryException;
	}

  /**
   * Returns true if all verification conditions passed to handle() since the
   * last call to reset() were valid.
   */
	SafeResult runIsValid();
  
  /**
   * Returns true if the labeled block is reachable
   */
  SafeResult runIsReachable();
  
  void setFeasibilityChecking(boolean b);
  
  /**
   * Prepare this encoder for a new path.
   */
  void reset();
  
  void setIterTimes(int iterTimes);

	void encode(PreProcessor<?> preprocessor, IRControlFlowGraph cfg, 
			LoopInfo loopInfo)
					throws PathFactoryException;

	void checkReach(PreProcessor<?> preprocessor, IRControlFlowGraph cfg, 
			LoopInfo loopInfo, String label)
					throws PathFactoryException;

	Pair<Boolean, StateExpression> encodeEdge(
			TraceFactory factory,
			IREdge<?> edge, StateExpression preState) 
					throws PathFactoryException;

	Pair<Boolean, StateExpression> checkReachBlock(
			TraceFactory factory,
			IRBasicBlock block,
      StateExpression preState, 
      String label) throws PathFactoryException;

	Pair<Boolean, StateExpression> encodeBlock(
			TraceFactory factory,
			IRBasicBlock block,
      StateExpression preState) throws PathFactoryException;

	IRTraceNode getErrorTrace(IRControlFlowGraph cfg);

	/** Enable check if okay to keep unrolling */
	void enableCheckKeepUnroll();
	
	/** Enable check if okay to exit unrolling */
	void enableCheckExitUnroll();

	/** Check if it is necessary to keep unrolling */
	boolean checkKeepUnroll() throws PathFactoryException;

	boolean checkExitUnroll() throws PathFactoryException;
}
