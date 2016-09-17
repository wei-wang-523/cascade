package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.Set;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;

class Parent {

	private final Set<ECR> parents;

	private Parent(Collection<ECR> parents) {
		this.parents = Sets.newLinkedHashSet(parents);
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
		return new Parent(Collections.singleton(ecr));
	}

	static Parent create(Collection<ECR> ecrs) {
		if (ecrs.isEmpty()) {
			return getBottom();
		} else {
			return new Parent(ecrs);
		}
	}

	/**
	 * Compute the least-upper-bound operators for two parents p1 and p2.
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
	ImmutableSet<ECR> getECRs() {
		return ImmutableSet.copyOf(parents);
	}

	Parent removeParent(ECR parent) {
		if (parents.isEmpty())
			return botInstance;

		Collection<ECR> new_parents = Sets.newHashSet();
		Iterator<ECR> parentItr = parents.iterator();
		while (parentItr.hasNext()) {
			ECR ecr = parentItr.next();
			if (ecr.equals(parent)) {
				continue;
			} else {
				new_parents.add(ecr);
			}
		}

		return Parent.create(new_parents);
	}
	
	boolean isEmpty() {
		return parents.isEmpty();
	}
}
