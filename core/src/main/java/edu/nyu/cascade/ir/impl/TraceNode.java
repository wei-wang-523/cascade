package edu.nyu.cascade.ir.impl;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import xtc.tree.Printer;

import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRStatement;
import edu.nyu.cascade.ir.IRTraceNode;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TheoremProver;

public class TraceNode implements IRTraceNode {
	private static BigInteger nextId = BigInteger.ZERO;
	private static final String EDGE = "Edge";

	private final List<IRStatement> stmts = Lists.newArrayList();
	private final List<TraceNode> successors = Lists.newArrayList();
	private final Map<IRStatement, Expression> stmtTraceExprMap = Maps
			.newHashMap();
	private final Map<IRStatement, Boolean> edgeStmtMap = Maps.newHashMap();
	private final Set<String> labels = Sets.newHashSet();

	private final BigInteger id;

	TraceNode(boolean isEdge) {
		this.id = nextId;
		if (isEdge)
			labels.add(EDGE);
		nextId = nextId.add(BigInteger.ONE);
	}

	@Override
	public List<IRStatement> getStatements() {
		return Collections.unmodifiableList(stmts);
	}

	@Override
	public List<? extends TraceNode> getSuccessors() {
		return Collections.unmodifiableList(successors);
	}

	@Override
	public Expression getTraceExpr(IRStatement stmt) {
		return stmtTraceExprMap.get(stmt);
	}

	@Override
	public boolean hasSuccessor() {
		return !successors.isEmpty();
	}

	@Override
	public void addSuccessor(IRTraceNode succ) {
		successors.add((TraceNode) succ);
	}

	@Override
	public void filterSuccessor(final ExpressionManager exprManager) {
		evalueateTraceExpr(exprManager);

		if (!hasSuccessor())
			return;

		TraceNode succ;

		if (!labels.contains(EDGE)) {
			final TheoremProver theoremProver = exprManager.getTheoremProver();
			succ = Iterables.find(successors, new Predicate<TraceNode>() {
				@Override
				public boolean apply(TraceNode succ) {
					if (!succ.hasGuard())
						return false;
					Expression value = theoremProver.evaluate(succ.getGuard());
					return value.asBooleanExpression().equals(exprManager.tt());
				}
			}, successors.get(0));

			successors.clear();
			successors.add(succ);
		} else {
			assert (successors.size() == 1);
			succ = successors.get(0);
		}

		succ.filterSuccessor(exprManager);
	}

	private boolean hasGuard() {
		Preconditions.checkArgument(labels.contains(EDGE));
		return !stmts.isEmpty();
	}

	private Expression getGuard() {
		Preconditions.checkArgument(labels.contains(EDGE));
		return stmtTraceExprMap.get(stmts.get(0));
	}

	@Override
	public void setStmtTraceExpr(IRStatement stmt, Expression expr) {
		if (expr != null)
			stmtTraceExprMap.put(stmt, expr);
	}

	@Override
	public boolean isEdge(IRStatement stmt) {
		return edgeStmtMap.containsKey(stmt);
	}

	@Override
	public void isNegate(IRStatement stmt, boolean isNegate) {
		edgeStmtMap.put(stmt, isNegate);
	}

	@Override
	public boolean isEdgeNegated(IRStatement stmt) {
		return edgeStmtMap.get(stmt);
	}

	@Override
	public void addStatements(Collection<? extends IRStatement> stmts) {
		this.stmts.addAll(stmts);
	}

	@Override
	public BigInteger getId() {
		return id;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append(id).append(" ").append(
				labels);
		return sb.toString();
	}

	@Override
	public void addLabels(Collection<String> _labels) {
		labels.addAll(_labels);
	}

	@Override
	public void format(Printer printer) {
		printer.pln().pln("Trace Node " + toString() + ": ").incr();

		for (IRStatement stmt : stmts) {
			printer.indent();
			printer.p(stmt.toString());
			if (stmtTraceExprMap.containsKey(stmt)) {
				Expression traceExpr = stmtTraceExprMap.get(stmt);
				printer.p(" [ ").p(traceExpr.toString()).p(" ]");
			}
			printer.pln();
		}

		for (IRTraceNode succ : successors) {
			printer.indent().pln(id + " " + "-->" + " " + succ.getId());
		}

		printer.decr();

		for (IRTraceNode succ : successors) {
			succ.format(printer);
		}
	}

	private void evalueateTraceExpr(final ExpressionManager exprManager) {
		if (stmtTraceExprMap.isEmpty())
			return;

		final TheoremProver theoremProver = exprManager.getTheoremProver();
		Collection<IRStatement> statements = Collections.unmodifiableSet(
				stmtTraceExprMap.keySet());
		for (IRStatement stmt : statements) {
			Expression traceExpr = stmtTraceExprMap.get(stmt);
			Expression traceExprPrime = theoremProver.evaluate(traceExpr);
			stmtTraceExprMap.put(stmt, traceExprPrime);
		}
	}
}
