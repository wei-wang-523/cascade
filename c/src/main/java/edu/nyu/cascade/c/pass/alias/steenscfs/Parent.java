package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import com.google.common.collect.Sets;

class Parent {

	private final Set<ECR> parents;

	private Parent(Set<ECR> parents) {
		this.parents = parents;
	}

	private static Parent botInstance = null;

	/**
	 * Get the parent with uninitialized ecr for blank type only
	 */
	static Parent getBottom() {
		if (botInstance != null)
			return botInstance;
		botInstance = new Parent(Collections.<ECR> emptySet());
		return botInstance;
	}

	/**
	 * Create the parent as <code>ecr</code>
	 */
	static Parent create(ECR ecr) {
		return new Parent(Sets.newHashSet(ecr));
	}

	static Parent create(Collection<ECR> ecrs) {
		if (ecrs.isEmpty())
			return getBottom();
		return new Parent(Sets.newHashSet(ecrs));
	}

	/**
	 * Compute the least-upper-bound operators for two parents <code>p1</code> and
	 * <code>p2</code>
	 */
	static Parent getLUB(Parent p1, Parent p2) {
		Set<ECR> ecrs = Sets.union(p1.getECRs(), p2.getECRs());
		return create(ecrs);
	}

	@Override
	public String toString() {
		return parents.toString();
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof Parent))
			return false;
		Parent that = (Parent) o;
		Set<ECR> diff1 = Sets.difference(this.getECRs(), that.getECRs());
		Set<ECR> diff2 = Sets.difference(that.getECRs(), this.getECRs());
		return diff1.isEmpty() && diff2.isEmpty();
	}

	/**
	 * Always return the root of ECR
	 */
	Set<ECR> getECRs() {
		Set<ECR> ecrs = Sets.newHashSet();
		for (ECR ecr : parents) {
			ecr = (ECR) ecr.findRoot();
			ecrs.add(ecr);
		}
		return ecrs;
	}

	Parent removeECR(ECR parent) {
		if (parents.isEmpty()) return this;

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
