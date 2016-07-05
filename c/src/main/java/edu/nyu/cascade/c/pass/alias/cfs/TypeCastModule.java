package edu.nyu.cascade.c.pass.alias.cfs;

import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

public class TypeCastModule {
	/**
	 * typeCastEdges tracks the type casting operations. Within each entry
	 * (target, source), then there is cast from source to target.
	 */
	private Map<Cell, Cell> typeCastEdges = Maps.newHashMap();

	void put(Cell oldCell, Cell newCell) {
		Preconditions.checkArgument(!typeCastEdges.containsKey(newCell));
		typeCastEdges.put(newCell, oldCell);
	}

	Cell get(Cell cell) {
		Preconditions.checkArgument(typeCastEdges.containsKey(cell));
		return typeCastEdges.get(cell);
	}
}
