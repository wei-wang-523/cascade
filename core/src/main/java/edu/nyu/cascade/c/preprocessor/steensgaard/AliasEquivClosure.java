package edu.nyu.cascade.c.preprocessor.steensgaard;

import com.google.common.collect.Iterables;

import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.c.preprocessor.IREquivClosure;

public class AliasEquivClosure implements IREquivClosure {
	final String name;
	final IRVar repVar;
	final Iterable<IRVar> elements;
	
	private AliasEquivClosure(IRVar repVar, Iterable<IRVar> elements) {
		this.name = new StringBuilder().append(repVar.getName()).append(repVar.getScopeName()).toString();
		this.repVar = repVar;
		this.elements = elements;
	}
	
	public static AliasEquivClosure create(IRVar repVar, Iterable<IRVar> elements) {
		return new AliasEquivClosure(repVar, elements);
	}

	public IRVar getRepVar() {
		return repVar;
	}

	@Override
	public Iterable<IRVar> getElements() {
		return elements;
	}
	
	@Override
	public String getName() {
		return name;
	}
	
	@Override
	public boolean hasElements() {
		return elements == null || Iterables.isEmpty(elements);
	}
	
}
