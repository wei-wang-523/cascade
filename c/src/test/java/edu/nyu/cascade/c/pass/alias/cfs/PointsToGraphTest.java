package edu.nyu.cascade.c.pass.alias.cfs;

import static org.junit.Assert.*;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import xtc.type.PointerT;
import xtc.type.VoidT;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.pass.alias.cfs.Cell;
import edu.nyu.cascade.c.pass.alias.cfs.CellManager;
import edu.nyu.cascade.c.pass.alias.cfs.PointsToGraph;
import edu.nyu.cascade.util.UnionFind;

public class PointsToGraphTest {
	private static final long PtrSize = CType.getInstance()
			.getSize(new PointerT(VoidT.TYPE));

	private CellManager cellManager;
	private PointsToGraph pointsToGraph;
	private UnionFind<?> uf;

	@Before
	public void setUp() throws Exception {
		pointsToGraph = new PointsToGraph();
		uf = UnionFind.create();
		cellManager = new CellManager();
	}

	@After
	public void tearDown() {
		pointsToGraph.clear();
		uf.reset();
	}

	@Test
	public void testPointsTo() {
		Cell s1 = cellManager.scalar(PtrSize);
		Cell s2 = cellManager.scalar(1000);
		pointsToGraph.put(s1, s2);

		Cell pointsCell = pointsToGraph.get(s1);
		assertTrue(pointsCell.equals(s2));
	}

	@Test(expected = IllegalArgumentException.class)
	public void testPointsToFail() {
		Cell s1 = cellManager.scalar(PtrSize);
		Cell s2 = cellManager.scalar(2000);
		Cell s3 = cellManager.scalar(1000);

		pointsToGraph.put(s1, s2);
		pointsToGraph.put(s1, s3);
	}

	@Test
	public void testPropagateEquivNoChange() {
		Cell s1 = cellManager.scalar(PtrSize);
		Cell s2 = cellManager.scalar(1000);
		Cell s3 = cellManager.scalar(PtrSize);
		Cell s4 = cellManager.scalar(2000);

		pointsToGraph.put(s1, s2);
		pointsToGraph.put(s3, s4);
		assertFalse(pointsToGraph.propagateEquivFully(uf));
	}

	@Test
	public void testPropagateEquivChange() {
		Cell s1 = cellManager.scalar(PtrSize);
		Cell s2 = cellManager.scalar(1000);
		Cell s3 = cellManager.scalar(PtrSize);
		Cell s4 = cellManager.scalar(2000);

		pointsToGraph.put(s1, s2);
		pointsToGraph.put(s3, s4);
		uf.union(s1, s3);
		assertTrue(pointsToGraph.propagateEquivFully(uf));
		assertEquals(s2, s4);
		assertEquals(s4, pointsToGraph.get(s1));
		assertEquals(s2, pointsToGraph.get(s3));
	}

	@Test
	public void testPropagateEquivCycleChange() {
		Cell s1 = cellManager.scalar(PtrSize);
		Cell s2 = cellManager.scalar(PtrSize);
		Cell s3 = cellManager.scalar(PtrSize);
		Cell s4 = cellManager.scalar(PtrSize);
		Cell s5 = cellManager.scalar(PtrSize);
		Cell s6 = cellManager.scalar(PtrSize);

		pointsToGraph.put(s1, s2);
		pointsToGraph.put(s3, s4);
		pointsToGraph.put(s2, s5);
		pointsToGraph.put(s4, s6);
		uf.union(s1, s3);
		assertTrue(pointsToGraph.propagateEquivFully(uf));
		assertEquals(s2, s4);
		assertEquals(s5, s6);
	}
}
