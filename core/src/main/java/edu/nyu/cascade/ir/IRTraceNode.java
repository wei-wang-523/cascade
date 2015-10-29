package edu.nyu.cascade.ir;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;

import xtc.tree.Printer;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;

public interface IRTraceNode {
	
	void addSuccessor(IRTraceNode succ);
	
	void filterSuccessor(ExpressionManager exprManager);

	List<? extends IRTraceNode> getSuccessors();
	
	boolean hasSuccessor();
	
	void addStatements(Collection<? extends IRStatement> stmts);
	
	void setStmtTraceExpr(IRStatement stmt, Expression traceExpr);
	
	void format(Printer printer);

	BigInteger getId();

	List<IRStatement> getStatements();

	Expression getTraceExpr(IRStatement stmt);

	void addLabels(Collection<String> preLabels);

	void isNegate(IRStatement stmt, boolean isNegate);

	boolean isEdgeNegated(IRStatement stmt);
	
	boolean isEdge(IRStatement stmt);
}
