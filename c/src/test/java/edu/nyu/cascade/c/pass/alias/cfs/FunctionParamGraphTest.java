package edu.nyu.cascade.c.pass.alias.cfs;

import static org.junit.Assert.*;

import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import com.google.common.collect.Lists;

import xtc.type.PointerT;
import xtc.type.VoidT;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.pass.alias.cfs.Cell;
import edu.nyu.cascade.c.pass.alias.cfs.CellManager;
import edu.nyu.cascade.c.pass.alias.cfs.FunctionParamGraph;
import edu.nyu.cascade.util.UnionFind;

public class FunctionParamGraphTest {
	private static final long PtrSize = CType.getInstance().getSize(new PointerT(
			VoidT.TYPE));

	private FunctionParamGraph funcGraph;
	private CellManager cellManager;
	private UnionFind<?> uf;

	@Before
	public void setUp() throws Exception {
		funcGraph = new FunctionParamGraph();
		uf = UnionFind.create();
		cellManager = new CellManager();
	}

	@After
	public void tearDown() throws Exception {
		funcGraph.clear();
		uf.reset();
	}

	@Test
	public void test() {
		Cell funcCell = cellManager.function();
		Cell returnCell = cellManager.scalar(PtrSize);
		Cell param1Cell = cellManager.scalar(PtrSize);
		Cell param2Cell = cellManager.scalar(PtrSize);
		List<Cell> paramCells = Lists.newArrayList(returnCell, param1Cell,
				param2Cell);
		funcGraph.put(funcCell, paramCells);
		assertEquals(1, funcGraph.getSize());
	}

	@Test(expected = IllegalArgumentException.class)
	public void testFailFuncCell() {
		Cell funcCell = cellManager.scalar(PtrSize);
		Cell returnCell = cellManager.scalar(PtrSize);
		Cell param1Cell = cellManager.scalar(PtrSize);
		Cell param2Cell = cellManager.scalar(PtrSize);
		List<Cell> paramCells = Lists.newArrayList(returnCell, param1Cell,
				param2Cell);
		funcGraph.put(funcCell, paramCells);
	}

	@Test
	public void testEquivPropagateNoChange() {
		Cell func1Cell = cellManager.function();
		{
			Cell returnCell = cellManager.scalar(PtrSize);
			Cell param1Cell = cellManager.scalar(PtrSize);
			Cell param2Cell = cellManager.scalar(PtrSize);
			List<Cell> paramCells = Lists.newArrayList(returnCell, param1Cell,
					param2Cell);
			funcGraph.put(func1Cell, paramCells);
		}

		Cell func2Cell = cellManager.function();
		{
			Cell returnCell = cellManager.scalar(PtrSize);
			Cell param1Cell = cellManager.scalar(PtrSize);
			Cell param2Cell = cellManager.scalar(PtrSize);
			List<Cell> paramCells = Lists.newArrayList(returnCell, param1Cell,
					param2Cell);
			funcGraph.put(func2Cell, paramCells);
		}

		assertFalse(funcGraph.propagateEquivFully(uf));
	}

	@Test
	public void testEquivPropagateChangeSameParamSize() {
		Cell func1Cell = cellManager.function();
		{
			Cell return1Cell = cellManager.scalar(PtrSize);
			Cell param1Cell = cellManager.scalar(PtrSize);
			Cell param2Cell = cellManager.scalar(PtrSize);
			List<Cell> param1Cells = Lists.newArrayList(return1Cell, param1Cell,
					param2Cell);
			funcGraph.put(func1Cell, param1Cells);
		}

		Cell func2Cell = cellManager.function();
		{
			Cell return2Cell = cellManager.scalar(PtrSize);
			Cell param3Cell = cellManager.scalar(PtrSize);
			Cell param4Cell = cellManager.scalar(PtrSize);
			List<Cell> param2Cells = Lists.newArrayList(return2Cell, param3Cell,
					param4Cell);
			funcGraph.put(func2Cell, param2Cells);
		}

		uf.union(func1Cell, func2Cell);
		assertTrue(funcGraph.propagateEquivFully(uf));
	}

	@Test
	public void testEquivPropagateChangeDiffParamSize() {
		Cell func1Cell = cellManager.function();
		Cell return1Cell = cellManager.scalar(PtrSize);
		Cell param1Cell = cellManager.scalar(PtrSize);
		Cell param2Cell = cellManager.scalar(PtrSize);
		List<Cell> param1Cells = Lists.newArrayList(return1Cell, param1Cell,
				param2Cell);
		funcGraph.put(func1Cell, param1Cells);

		Cell func2Cell = cellManager.function();
		Cell return2Cell = cellManager.scalar(PtrSize);
		Cell param3Cell = cellManager.scalar(PtrSize);
		List<Cell> param2Cells = Lists.newArrayList(return2Cell, param3Cell);
		funcGraph.put(func2Cell, param2Cells);

		uf.union(func1Cell, func2Cell);
		assertTrue(funcGraph.propagateEquivFully(uf));

		int minParamSize = Math.min(param1Cells.size(), param2Cells.size());
		for (int i = 0; i < minParamSize; ++i) {
			assertEquals(param1Cells.get(i), param2Cells.get(i));
		}
	}
}
