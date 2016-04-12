package edu.nyu.cascade.c.pass.alias.cfs;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import edu.nyu.cascade.c.pass.alias.cfs.Cell;
import edu.nyu.cascade.c.pass.alias.cfs.CellManager;

public class CellTest {
	private CellManager cellManager;
	
	@Before
	public void setup() {
		cellManager = new CellManager();
	}
	
	@Test
	public void testBottom() {
		Cell s1 = cellManager.bottom();
		assertTrue(cellManager.isBottom(s1));
		assertTrue(s1.getSize() == 0);
	}

	@Test
	public void testScalar() {
		Cell s1 = cellManager.scalar(1000);
		assertTrue(cellManager.isScalar(s1));
		assertTrue(s1.getSize() == 1000);
	}
	
	@Test
	public void testStruct() {
		Cell s1 = cellManager.struct(1000);
		assertTrue(cellManager.isStruct(s1));
		assertTrue(s1.getSize() == 1000);
	}
	
	@Test
	public void testFunction() {
		Cell s1 = cellManager.function();
		assertTrue(cellManager.isFunction(s1));
		assertTrue(s1.getSize() == 0);
	}
}
