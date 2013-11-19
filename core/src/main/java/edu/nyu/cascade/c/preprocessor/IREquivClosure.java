package edu.nyu.cascade.c.preprocessor;

public interface IREquivClosure {
	
	String getName();

	Iterable<IRVar> getElements();
	
	boolean hasElements();

	Object getProperty(String name);
	
	Object setProperty(String name, Object o);
}
