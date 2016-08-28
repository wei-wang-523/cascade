package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import com.google.common.collect.Sets;

import edu.nyu.cascade.util.IOUtils;

class Parent {

	enum Kind {
		TOP, BOTTOM, SET,
	}

	private final Kind kind;
	private final Set<ECR> parents;

	private Parent(Kind kind, Set<ECR> parents) {
		this.kind = kind;
		for (ECR parent : parents) {
			if (!((ECR) parent.findRoot()).getType().isStruct())
				IOUtils.err().println("Invalid parent type");
		}
		this.parents = parents;
	}

	private static Parent botInstance = null, topInstance = null;

	/**
	 * Get the parent with uninitialized ecr for blank type only
	 * 
	 * @return
	 */
	static Parent getBottom() {
		if (botInstance != null)
			return botInstance;
		botInstance = new Parent(Kind.BOTTOM, Collections.<ECR> emptySet());
		return botInstance;
	}

	/**
	 * Create the parent as <code>ecr</code>
	 * 
	 * @param ecr
	 * @return
	 */
	static Parent create(ECR ecr) {
		return new Parent(Kind.SET, Sets.newHashSet(ecr));
	}

	static Parent create(Collection<ECR> ecrs) {
		if (ecrs.isEmpty())
			return getBottom();
		return new Parent(Kind.SET, Sets.newHashSet(ecrs));
	}

	/**
	 * Create the parent with no parent, while allowing use of least-upper-bound
	 * operators in the type inference algorithm
	 * 
	 * @return
	 */
	static Parent getTop() {
		if (topInstance != null)
			return topInstance;
		topInstance = new Parent(Kind.TOP, Collections.<ECR> emptySet());
		return topInstance;
	}

	/**
	 * Compute the least-upper-bound operators for two parents <code>p1</code> and
	 * <code>p2</code>
	 * 
	 * @param p1
	 * @param p2
	 * @return
	 */
	static Parent getLUB(Parent p1, Parent p2) {
		Parent top = getTop();
		if (p1.isTop() || p2.isTop())
			return top;
		if (p1.isBottom())
			return p2;
		if (p2.isBottom())
			return p1;

		Set<ECR> ecrs = Sets.union(p1.getECRs(), p2.getECRs());
		return create(ecrs);
	}

	@Override
	public String toString() {
		switch (kind) {
		case BOTTOM:
			return String.valueOf('\u22A5');
		case TOP:
			return String.valueOf('\u22A4');
		default: {
			Set<ECR> ecrs = getECRs();
			return ecrs.toString();
		}
		}
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof Parent))
			return false;
		Parent that = (Parent) o;
		if (!kind.equals(that.kind))
			return false;
		if (!kind.equals(Kind.SET))
			return true;
		Set<ECR> diff = Sets.difference(this.getECRs(), that.getECRs());
		return diff.isEmpty();
	}

	boolean isBottom() {
		return Kind.BOTTOM.equals(kind);
	}

	boolean isTop() {
		return Kind.TOP.equals(kind);
	}

	/**
	 * Always return the root of ECR
	 * 
	 * @return
	 */
	Set<ECR> getECRs() {
		Set<ECR> ecrs = Sets.newHashSet();
		for (ECR ecr : parents) {
			ecr = (ECR) ecr.findRoot();
			if (!ecr.getType().isStruct())
				IOUtils.err().println("Invalid parent type");
			ecrs.add(ecr);
		}
		return ecrs;
	}

	Parent removeECR(ECR parent) {
		if (kind.equals(Kind.TOP) || kind.equals(Kind.BOTTOM))
			return this;

		Set<ECR> ecrs = Sets.newHashSet(parents);
		for (ECR ecr : parents) {
			if (ecr.equals(parent)) {
				ecrs.remove(ecr);
				if (ecrs.isEmpty())
					return botInstance;
				return Parent.create(parents);
			}
		}

		return this;
	}

	void clear() {
		parents.clear();
	}
}
