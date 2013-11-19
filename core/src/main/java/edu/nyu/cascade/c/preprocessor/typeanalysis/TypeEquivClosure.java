package edu.nyu.cascade.c.preprocessor.typeanalysis;

import java.util.Map;

import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.preprocessor.IREquivClosure;
import edu.nyu.cascade.c.preprocessor.IRVar;

public class TypeEquivClosure implements IREquivClosure {
	
	String name;
	final Iterable<IRVar> elements;
	final Map<String, Object> properties;
	
	private TypeEquivClosure(String name, Iterable<IRVar> elements) {
		this.name = name;
		this.elements = elements;
		this.properties = Maps.newHashMap();
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
	
	@Override
	public boolean hasElements() {
		return elements == null || Iterables.isEmpty(elements);
	}

	@Override
	public Object getProperty(String name) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public Object setProperty(String name, Object o) {
		// TODO Auto-generated method stub
		return null;
	}

}
