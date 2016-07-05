package edu.nyu.cascade.c.util;

import com.google.inject.Guice;
import com.google.inject.Injector;

import edu.nyu.cascade.c.CModule;
import edu.nyu.cascade.util.CascadeModule;

public class TestUtils extends edu.nyu.cascade.util.TestUtils {

	public static Injector getInjector() {
		return Guice.createInjector(new CModule(), new CascadeModule());
	}
}
