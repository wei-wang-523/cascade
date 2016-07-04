package edu.nyu.cascade.ir.pass;

import java.util.Collection;
import edu.nyu.cascade.ir.IRControlFlowGraph;

/**
 * Pre-analysis statement
 * 
 * @author Wei
 *
 */
public interface IRPass {

	/**
	 * Analysis control flow graphs <code>globalCFG</code> and <code>CFGs</code>
	 */
	void analysis(IRControlFlowGraph globalCFG,
	    Collection<IRControlFlowGraph> CFGs);

	void reset();
}
