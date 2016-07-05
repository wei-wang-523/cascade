package edu.nyu.cascade.c.pass.alias.cfs;

import java.util.Map;
import java.util.Map.Entry;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.util.UnionFind;

/**
 * PointsToGraph is built during the program parsing by CellEncoder.
 * outgoingEdges keep the points-to edges from cell to cell. partitionView keep
 * the points-to edge from partition to partition.
 * 
 * outgoingEdges are untouched after parsing. partitionView will be simplified
 * after equivalence relation propagation, and it will be added new edges after
 * ccjoin equivalence relation propagation.
 * 
 * @author Wei
 *
 */

public class PointsToGraph {
	Map<Cell, Cell> outgoingEdges = Maps.newHashMap();

	void clear() {
		outgoingEdges.clear();
	}

	void put(Cell s1, Cell s2) {
		Preconditions.checkArgument(!outgoingEdges.containsKey(s1));
		outgoingEdges.put(s1, s2);
	}

	Cell get(Cell s1) {
		Preconditions.checkArgument(outgoingEdges.containsKey(s1));
		return outgoingEdges.get(s1);
	}

	boolean has(Cell from) {
		return outgoingEdges.containsKey(from);
	}

	/**
	 * Propagate equivalence relation between cells in outgoingEdges by merging
	 * the entries with equivalent keys until saturated.
	 * 
	 * @param uf
	 * @return
	 */
	boolean propagateEquivFully(UnionFind<?> uf) {
		boolean changed = false;
		boolean hasNewlyGeneratedEquiv = false;
		do {
			hasNewlyGeneratedEquiv = propagateEquiv(uf);
			changed |= hasNewlyGeneratedEquiv;
		} while (hasNewlyGeneratedEquiv);
		return changed;
	}

	int getSize() {
		return outgoingEdges.size();
	}

	/**
	 * Helper method of propagateEquivalenceFully. Simplify the partitionView map
	 * by merging the entries with equivalent keys, and further unify their values
	 * (newly generated equiv relations for the next round propagation).
	 * 
	 * @param uf
	 * @return
	 */
	private boolean propagateEquiv(UnionFind<?> uf) {
		Map<Cell, Cell> newView = Maps.newHashMap();
		boolean hasNewEquiv = false;
		for (Entry<Cell, Cell> entry : outgoingEdges.entrySet()) {
			Cell key = entry.getKey();
			Cell value = entry.getValue();
			if (newView.containsKey(key)) {
				hasNewEquiv |= uf.union(newView.get(key), value);
			} else {
				newView.put(key, value);
			}
		}
		outgoingEdges = newView;
		return hasNewEquiv;
	}
}
