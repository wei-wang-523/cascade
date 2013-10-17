package edu.nyu.cascade.c.preprocessor.typeanalysis;

import edu.nyu.cascade.c.preprocessor.IREquivClosure;
import edu.nyu.cascade.c.preprocessor.IRVar;

public class TypeEquivClosure implements IREquivClosure {
	
	String name;
	final Iterable<IRVar> elements;
	
	private TypeEquivClosure(String name, Iterable<IRVar> elements) {
		this.name = name;
		this.elements = elements;
	}
	
	public static TypeEquivClosure create(String name, Iterable<IRVar> elements) {
		return new TypeEquivClosure(name, elements);
	}

	@Override
  public String getName() {
		return name;
  }

	@Override
  public Iterable<IRVar> getElements() {
		return elements;
  }

}
