package edu.nyu.cascade.c.preprocessor;

public interface IREquivalentClosure {
	
	String getName();

	Iterable<IREquivalentVar> getElements();
}
