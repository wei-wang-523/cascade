package edu.nyu.cascade.c.preprocessor.cfs;

import static org.junit.Assert.*;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import xtc.type.PointerT;
import xtc.type.VoidT;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.util.UnionFind;

public class CCjoinGraphTest {
	private static long PtrSize =
			CType.getInstance().getSize(new PointerT(VoidT.TYPE));
	
	private CellManager cellManager;
	private CCjoinModule ccjoinModule;
	private UnionFind<?> uf;

	@Before
	public void setUp() throws Exception {
		uf = UnionFind.create();
		cellManager = new CellManager();
		ccjoinModule = new CCjoinModule();
	}

	@After
	public void tearDown() throws Exception {
		ccjoinModule.clear();
		uf.reset();
	}

	@Test
	public void test() {
		Cell rhsCell = cellManager.scalar(PtrSize);
		Cell lhsCell1 = cellManager.scalar(PtrSize);
		Cell lhsCell2 = cellManager.scalar(PtrSize);
		ccjoinModule.put(rhsCell, lhsCell1);
		ccjoinModule.put(rhsCell, lhsCell2);
	}

	@Test(expected=IllegalArgumentException.class)
	public void testFailOnStructLHS() {
		Cell rhsCell = cellManager.scalar(PtrSize);
		Cell lhsCell1 = cellManager.struct(PtrSize);
		Cell lhsCell2 = cellManager.scalar(PtrSize);
		ccjoinModule.put(rhsCell, lhsCell1);
		ccjoinModule.put(rhsCell, lhsCell2);
	}
	
	@Test(expected=IllegalArgumentException.class)
	public void testFailOnStructRHS() {
		Cell rhsCell = cellManager.struct(PtrSize);
		Cell lhsCell1 = cellManager.scalar(PtrSize);
		Cell lhsCell2 = cellManager.scalar(PtrSize);
		ccjoinModule.put(rhsCell, lhsCell1);
		ccjoinModule.put(rhsCell, lhsCell2);
	}
	
	@Test
	public void testPointsToPropagate() {
		Cell c1 = cellManager.scalar(PtrSize);
		Cell c2 = cellManager.scalar(PtrSize);
		Cell c3 = cellManager.scalar(PtrSize);
		Cell c4 = cellManager.scalar(PtrSize);
		Cell c5 = cellManager.scalar(PtrSize);
		ccjoinModule.put(c1, c2);
		ccjoinModule.put(c2, c1);
		ccjoinModule.put(c3, c4);
		ccjoinModule.put(c4, c5);
		ccjoinModule.put(c5, c4);
		
		Cell pc2 = cellManager.scalar(PtrSize);
		Cell pc5 = cellManager.scalar(PtrSize);
		PointsToGraph pointsToGraph = new PointsToGraph();
		pointsToGraph.put(c2, pc2);
		pointsToGraph.put(c5, pc5);
		
		assertTrue(ccjoinModule.propagatePointsTo(uf, pointsToGraph));
		assertFalse(ccjoinModule.has(c1));
		assertFalse(ccjoinModule.has(c2));
		assertFalse(ccjoinModule.has(c4));
		assertFalse(ccjoinModule.has(c5));
		assertTrue(ccjoinModule.has(c3));
	}
	
	@Test
	public void testPointsToPropagateUnifiedPointsToPart() {
		Cell c1 = cellManager.scalar(PtrSize);
		Cell c2 = cellManager.scalar(PtrSize);
		Cell c3 = cellManager.scalar(PtrSize);
		Cell c4 = cellManager.scalar(PtrSize);
		Cell c5 = cellManager.scalar(PtrSize);
		ccjoinModule.put(c1, c2);
		ccjoinModule.put(c2, c3);
		ccjoinModule.put(c3, c4);
		ccjoinModule.put(c4, c5);
		ccjoinModule.put(c5, c4);
		
		Cell pc2 = cellManager.scalar(PtrSize);
		Cell pc5 = cellManager.scalar(PtrSize);
		PointsToGraph pointsToGraph = new PointsToGraph();
		pointsToGraph.put(c2, pc2);
		pointsToGraph.put(c5, pc5);
		
		assertTrue(ccjoinModule.propagatePointsTo(uf, pointsToGraph));
		assertTrue(ccjoinModule.has(c1));
		assertFalse(ccjoinModule.has(c2));
		assertFalse(ccjoinModule.has(c3));
		assertFalse(ccjoinModule.has(c4));
		assertFalse(ccjoinModule.has(c5));
		assertEquals(pc2, pc5);
	}
}
