package edu.nyu.cascade.c.preprocessor;

public class EquivalentClass {
	final AliasVar repVar;
	final Iterable<AliasVar> elements;
	
	private EquivalentClass(AliasVar repVar, Iterable<AliasVar> elements) {
		this.repVar = repVar;
		this.elements = elements;
	}
	
	public static EquivalentClass create(AliasVar repVar, Iterable<AliasVar> elements) {
		return new EquivalentClass(repVar, elements);
	}

	public AliasVar getRepVar() {
		return repVar;
	}

	public Iterable<AliasVar> getElements() {
		return elements;
	}	
}
