package edu.nyu.cascade.c.preprocessor.steensgaard;

import edu.nyu.cascade.c.preprocessor.IREquivalentVar;
import edu.nyu.cascade.c.preprocessor.IREquivalentClosure;

public class AliasEquivalentClosure implements IREquivalentClosure {
	final String name;
	final IREquivalentVar repVar;
	final Iterable<IREquivalentVar> elements;
	
	private AliasEquivalentClosure(IREquivalentVar repVar, Iterable<IREquivalentVar> elements) {
		this.name = new StringBuilder().append(repVar.getName()).append(repVar.getScope()).toString();
		this.repVar = repVar;
		this.elements = elements;
	}
	
	public static AliasEquivalentClosure create(IREquivalentVar repVar, Iterable<IREquivalentVar> elements) {
		return new AliasEquivalentClosure(repVar, elements);
	}

	public IREquivalentVar getRepVar() {
		return repVar;
	}

	@Override
	public Iterable<IREquivalentVar> getElements() {
		return elements;
	}
	
	@Override
	public String getName() {
		return name;
	}
	
}
