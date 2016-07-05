package edu.nyu.cascade.c.pass.alias.cfs;

import java.util.Collection;
import java.util.List;
import com.google.common.base.Preconditions;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;

import edu.nyu.cascade.util.UnionFind;

/**
 * CCjoinModule contains a directed cyclic graph to record the ccjoin relation
 * between cells. For each entry (rhs, lhs), then both rhs and lhs must be
 * SCALAR cell. If rhs has points-to cell rhs' and lhs must points-to rhs' too.
 * 
 * @author weiwang
 *
 */
class CCjoinModule {
	Multimap<Cell, Cell> ccjoinEdges = HashMultimap.create();

	/**
	 * Update ccjoinEdges. Check fails if c1 and c2 are not STRUCT.
	 * 
	 * @param c1
	 * @param c2
	 */
	void put(Cell c1, Cell c2) {
		Preconditions.checkArgument(!c1.getKind().equals(Cell.CellKind.STRUCT));
		Preconditions.checkArgument(!c2.getKind().equals(Cell.CellKind.STRUCT));
		ccjoinEdges.put(c1, c2);
	}

	Collection<Cell> get(Cell from) {
		Preconditions.checkArgument(ccjoinEdges.containsKey(from));
		return ccjoinEdges.get(from);
	}

	boolean has(Cell from) {
		return ccjoinEdges.containsKey(from);
	}

	void clear() {
		ccjoinEdges.clear();
	}

	boolean propagatePointsTo(UnionFind<?> uf, PointsToGraph pointsToGraph) {
		boolean changed = false;

		Collection<Cell> visited = Sets.newHashSet();

		List<Cell> workList = Lists.newArrayList();
		workList.addAll(ccjoinEdges.keySet());

		while (!workList.isEmpty()) {
			Cell curr = workList.remove(0);
			if (visited.contains(curr))
				continue;
			visited.add(curr);

			// No points-to partition, continue.
			if (!pointsToGraph.has(curr))
				continue;

			// Current cell curr has points-to partition.
			// Collected all the cells reachable from curr in collectedRemoveCells.
			// Remove collectedRemoveCells from ccjoinEdges, and update points-to
			// graph with newly-added points-to edge between the partitions of
			// collectedRemoveCells and the points-to partition of currPart.
			Collection<Cell> collectedRemoveCells = Sets.newHashSet();

			List<Cell> removeWorkList = Lists.newArrayList();
			removeWorkList.add(curr);

			while (!removeWorkList.isEmpty()) {
				Cell currRemove = removeWorkList.remove(0);
				if (collectedRemoveCells.contains(currRemove))
					continue;
				collectedRemoveCells.add(currRemove);
				removeWorkList.addAll(ccjoinEdges.removeAll(currRemove));
			}

			visited.addAll(collectedRemoveCells);

			// Add points-to edge from removeCell's partition to currPtrs2Part, if
			// the partition of removeCell has no points-to partition. Otherwise,
			// we unify its points-to partition with currPtrs2Part.
			Cell currPtrs2Cell = pointsToGraph.get(curr);
			for (Cell removeCell : collectedRemoveCells) {
				if (pointsToGraph.has(removeCell)) {
					Cell removePtrs2Cell = pointsToGraph.get(removeCell);
					changed |= uf.union(currPtrs2Cell, removePtrs2Cell);
				} else {
					pointsToGraph.put(removeCell, currPtrs2Cell);
					changed = true;
				}
			}
		}

		return changed;
	}
}
