package edu.nyu.cascade.c.pass.alias.cfs;

import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Range;
import com.google.common.collect.Table;

class ContainsGraph {
	Table<Cell, Range<Long>, Cell> containsEdge = HashBasedTable.create();

	void put(Cell from, long low, long high, Cell to) {
		Range<Long> offsetRange = Range.openClosed(low, high);
		if (containsEdge.contains(from, offsetRange)) {
			throw new IllegalArgumentException();
		}
		containsEdge.put(from, offsetRange, to);
	}

	Cell get(Cell from, long low, long high) {
		Range<Long> offsetRange = Range.openClosed(low, high);
		if (!containsEdge.contains(from, offsetRange)) {
			throw new IllegalArgumentException();
		}
		return containsEdge.get(from, offsetRange);
	}

	boolean has(Cell from, long low, long high) {
		Range<Long> offsetRange = Range.openClosed(low, high);
		return containsEdge.contains(from, offsetRange);
	}
}
