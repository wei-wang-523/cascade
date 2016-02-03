package edu.nyu.cascade.c.preprocessor.cfs;

import java.util.List;
import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.util.UnionFind;

class FunctionParamGraph {
	/**
	 * funcEdges tracks the function cell and its parameter cells.
	 * When propagate equivalence relation between function cells,
	 * all their parameter cells should be unified too. Remove the
	 * entries share the same function cells, but keep the one with
	 * maximum number of parameter cells.
	 */
	private Map<Cell, List<Cell>> funcEdges = Maps.newHashMap();
	
	/**
	 * Put function cell lambdaCell and its paramCells (the first one is the cell
	 * of the returned value) into funcEdges.
	 * Check fails if lambdaCell is not Function cell.
	 * @param lambdaCell
	 * @param paramCells
	 */
	void put(Cell lambdaCell, List<Cell> paramCells) {
		Preconditions.checkArgument(lambdaCell.getKind().equals(Cell.CellKind.FUNC));
	  Preconditions.checkArgument(!funcEdges.containsKey(lambdaCell));
	  funcEdges.put(lambdaCell, paramCells);
	}
	
	List<Cell> getParams(Cell lambdaCell) {
		Preconditions.checkArgument(funcEdges.containsKey(lambdaCell));
		return funcEdges.get(lambdaCell);
	}
	
	/**
	 * Propagate equivalence relation in funcEdges. Note that the equivalence
	 * relation derived from propagation may further be derived function
	 * equivalence.
	 * @param uf
	 * @return if the funcGraph has been updated.
	 */
	boolean propagateEquivFully(UnionFind<?> uf) {
		Map<Cell, List<Cell>> remainEdges = Maps.newHashMap();
		boolean changed = false;
		for(Map.Entry<Cell, List<Cell>> funcEntry : funcEdges.entrySet()) {
			Cell func = funcEntry.getKey();
			List<Cell> params = funcEntry.getValue();
			if(remainEdges.containsKey(func)) {
				List<Cell> representParams = remainEdges.get(func);
				int paramMinSize =  Math.min(params.size(), representParams.size());
				for(int i = 0; i < paramMinSize; ++i) {
					Cell representParam = representParams.get(i);
					Cell param = params.get(i);
					changed |= uf.union(representParam, param);
				}
			} else {
				remainEdges.put(func, params);
			}
		}
		return changed;
	}

	void clear() {
	  funcEdges.clear();
  }

	int getSize() {
	  return funcEdges.size();
  }
}
