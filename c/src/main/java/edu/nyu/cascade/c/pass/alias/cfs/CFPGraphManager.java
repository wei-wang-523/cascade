package edu.nyu.cascade.c.pass.alias.cfs;

import java.util.List;

public class CFPGraphManager {
	private PointsToGraph pointsToGraph = new PointsToGraph();
	private ContainsGraph containsGraph = new ContainsGraph();
	private FunctionParamGraph funcGraph = new FunctionParamGraph();
	private CCjoinModule ccjoinModule = new CCjoinModule();
	private TypeCastModule castModule = new TypeCastModule();

	void addPointsEdge(Cell from, Cell to) {
		pointsToGraph.put(from, to);
	}

	Cell getPointsCell(Cell from) {
		return pointsToGraph.get(from);
	}

	boolean hasPointsCell(Cell from) {
		return pointsToGraph.has(from);
	}

	void addFunctionEdge(Cell lambdaCell, List<Cell> paramCells) {
		funcGraph.put(lambdaCell, paramCells);
	}

	boolean hasContainsCell(Cell baseCell, long low, long high) {
		return containsGraph.has(baseCell, low, high);
	}

	Cell getContainsCell(Cell baseCell, long low, long high) {
		return containsGraph.get(baseCell, low, high);
	}

	void addContainsEdge(Cell baseCell, long low, long high, Cell fieldCell) {
		containsGraph.put(baseCell, low, high, fieldCell);
	}

	void addCCjoinEdge(Cell rhsCell, Cell lhsCell) {
		ccjoinModule.put(rhsCell, lhsCell);
	}

	void addTypeCastEdge(Cell oldCell, Cell newCell) {
		castModule.put(newCell, oldCell);
	}

	Cell getCastSourceCell(Cell cell) {
		return castModule.get(cell);
	}

}
