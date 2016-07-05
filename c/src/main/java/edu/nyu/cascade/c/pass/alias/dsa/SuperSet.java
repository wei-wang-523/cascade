package edu.nyu.cascade.c.pass.alias.dsa;

import java.util.Comparator;
import java.util.Set;
import java.util.SortedSet;

import com.google.common.collect.Sets;

/**
 * Super set of set. It is a sorted set ordered from smaller set to larger one.
 * 
 * @author Wei
 *
 * @param <T>
 */

class SuperSet<T> {
	SortedSet<Set<T>> TySS;

	SuperSet() {
		TySS = Sets.newTreeSet(new Comparator<Set<T>>() {
			@Override
			public int compare(Set<T> lhs, Set<T> rhs) {
				return Integer.compare(lhs.size(), rhs.size());
			}
		});
	}

	SuperSet(SuperSet<T> tySS) {
		TySS = Sets.newTreeSet(new Comparator<Set<T>>() {
			@Override
			public int compare(Set<T> lhs, Set<T> rhs) {
				return Integer.compare(lhs.size(), rhs.size());
			}
		});
		TySS.addAll(tySS.TySS);
	}

	/**
	 * addSet - Avoid to create duplicate sets. Return the existing set if TySet
	 * is contained in TySS; otherwise, add TySet to TySS and return TySet.
	 * 
	 * @param TySet
	 * @return
	 */
	Set<T> addSet(Set<T> TySet) {
		for (Set<T> element : TySS) {
			if (element.size() < TySet.size())
				continue;
			if (element.size() > TySet.size())
				break;
			if (element.containsAll(TySet) && TySet.containsAll(element)) {
				return element;
			}
		}

		TySS.add(TySet);
		return TySet;
	}
}
