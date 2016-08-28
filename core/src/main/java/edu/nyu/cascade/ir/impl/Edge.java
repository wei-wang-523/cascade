package edu.nyu.cascade.ir.impl;

import java.util.Collections;
import java.util.Set;

import xtc.tree.Node;
import xtc.tree.Printer;

import com.google.common.base.Objects;
import com.google.common.collect.Sets;

import edu.nyu.cascade.ir.IRBooleanExpression;
import edu.nyu.cascade.ir.IREdge;

public class Edge implements IREdge<BasicBlock> {
	static Edge create(BasicBlock currentBlock, BasicBlock succ) {
		return create(currentBlock, null, succ);
	}

	static Edge create(BasicBlock currentBlock, IRBooleanExpression guard,
			BasicBlock succ) {
		return new Edge(currentBlock, guard, succ);
	}

	private final BasicBlock source, target;
	private final IRBooleanExpression guard;

	private Edge(BasicBlock currentBlock, IRBooleanExpression guard,
			BasicBlock succ) {
		this.source = currentBlock;
		this.target = succ;
		this.guard = guard;
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof Edge)) {
			return false;
		}
		Edge edge = (Edge) o;
		return (edge != null && source.equals(edge.source)
				&& target.equals(edge.target) && Objects.equal(guard, edge.guard));
	}

	@Override
	public IRBooleanExpression getGuard() {
		// TODO: Is the guard mutable?
		return guard;
	}

	@Override
	public BasicBlock getSource() {
		return source;
	}

	@Override
	public Node getSourceNode() {
		return guard == null ? null : guard.getSourceNode();
	}

	@Override
	public BasicBlock getTarget() {
		return target;
	}

	@Override
	public int hashCode() {
		int sourceHash = source.hashCode();
		int edgeHash = guard == null ? 0 : guard.hashCode();
		int targetHash = target.hashCode();

		return sourceHash ^ edgeHash ^ targetHash;
	}

	@Override
	public void format(Printer printer) {
		printer.pln(toString());
	}

	@Override
	public String toString() {
		return getSource().getId() + " --"
				+ (guard == null ? "" : "[" + guard + "]") + "--> "
				+ getTarget().getId();
	}

	public static Set<BasicBlock> getSources(Iterable<Edge> edges) {
		Set<BasicBlock> preds = Sets.newHashSet();
		for (Edge edge : edges) {
			preds.add(edge.getSource());
		}
		return Collections.unmodifiableSet(preds);
	}

	public static Set<BasicBlock> getTargets(Iterable<Edge> edges) {
		Set<BasicBlock> preds = Sets.newHashSet();
		for (Edge edge : edges) {
			preds.add(edge.getTarget());
		}
		return Collections.unmodifiableSet(preds);
	}
}
