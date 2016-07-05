package edu.nyu.cascade.util;

import static edu.nyu.cascade.util.Identifiers.*;
import static org.junit.Assert.*;

import java.util.List;

import org.junit.Test;

import com.google.common.collect.Lists;

public class IdentifiersTest {
	private static final List<String> validCIds = Lists.newArrayList("x", "_",
			"__x", "x_y_z", "x0", "camelCaseId");
	private static final List<String> validIds = Lists.asList("x'", "a'b",
			validCIds.toArray(new String[0]));

	private static final List<String> invalidIds = Lists.newArrayList("0", "0x",
			"x.y", "a#b", "#", "f(x)");
	private static final List<String> invalidCIds = Lists.asList("x'", "a'b",
			invalidIds.toArray(new String[0]));

	@Test
	public void testIsValidId() {
		for (String id : validIds) {
			assertTrue(isValidId(id));
		}
	}

	@Test
	public void testIsValidId2() {
		for (String id : invalidIds) {
			assertFalse(isValidId(id));
		}
	}

	@Test
	public void testIsValidCId() {
		for (String id : validCIds) {
			assertTrue(isValidId(id, IdType.C));
		}
	}

	@Test
	public void testIsValidCId2() {
		for (String id : invalidCIds) {
			assertFalse(isValidId(id, IdType.C));
		}
	}

	@Test
	public void testIsValidSplId() {
		for (String id : validCIds) {
			assertTrue(isValidId(id, IdType.SPL));
		}
	}

	@Test
	public void testIsValidSplId2() {
		for (String id : invalidCIds) {
			assertFalse(isValidId(id, IdType.SPL));
		}
	}

	@Test
	public void testToValidId() {
		for (String id : validIds) {
			assertEquals(id, toValidId(id));
		}
	}

	@Test
	public void testToValidId2() {
		for (String id : invalidIds) {
			assertTrue(isValidId(toValidId(id)));
		}
	}

}
