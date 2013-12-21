package edu.nyu.cascade.c.preprocessor.steensgaard;

import java.util.Map;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ExecutionException;

import xtc.util.SymbolTable.Scope;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.Iterables;
import com.google.common.collect.MapMaker;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.c.preprocessor.IREquivClosure;
import edu.nyu.cascade.util.CacheException;
import edu.nyu.cascade.util.Identifiers;

public class AliasEquivClosure implements IREquivClosure {
	
  private static final LoadingCache<Steensgaard, ConcurrentMap<IRVar, AliasEquivClosure>> cache = CacheBuilder
      .newBuilder().build(
          new CacheLoader<Steensgaard, ConcurrentMap<IRVar, AliasEquivClosure>>(){
            public ConcurrentMap<IRVar, AliasEquivClosure> load(Steensgaard preprocessor) {
              return new MapMaker().makeMap();
            }
          });
	
	final String name;
	final IRVar repVar;
	final Iterable<IRVar> elements;
	final Map<String, Object> properties;
	
	private AliasEquivClosure(IRVar repVar, Iterable<IRVar> elements) {
		this.name = new StringBuilder().append(repVar.getName())
				.append(repVar.getScope().getName()).toString();
		this.repVar = repVar;
		this.elements = elements;
		this.properties = Maps.newLinkedHashMap();
		properties.put(Identifiers.SCOPE, getHighestScope(elements));
	}
	
    private Scope getHighestScope(Iterable<IRVar> elements) {
	Scope rootScope = null;
	for(IRVar elem : elements) {
	    if(rootScope == null) { 
		rootScope = elem.getScope();
	    } else {
		Scope elemScope = elem.getScope();
		if(elemScope.equals(rootScope)) continue;
		if(CScopeAnalyzer.isNestedOrEqual(rootScope, elemScope)) continue;
		
		if(CScopeAnalyzer.isNested(elemScope, rootScope)) {
		    // Replace rootScope with high level scope
		    rootScope = elemScope; continue;
		}
		
		while(!CScopeAnalyzer.isNestedOrEqual(rootScope, elemScope)) {
		    rootScope = rootScope.getParent();
		}
	    }
	}
	
	if(rootScope == null) {
	    throw new IllegalArgumentException("Root scope is null");
	}
	return rootScope;
    }

	public static AliasEquivClosure create(Steensgaard preprocessor, IRVar repVar) {
		Preconditions.checkArgument(preprocessor.getSnapShot() != null);
		Preconditions.checkArgument(preprocessor.getSnapShot().containsKey(repVar));
		try {
			if(cache.get(preprocessor).containsKey(repVar)) {
				return cache.get(preprocessor).get(repVar);
			}
			
		  Iterable<IRVar> elements = preprocessor.getSnapShot().get(repVar);
			AliasEquivClosure res = new AliasEquivClosure(repVar, elements);
			cache.get(preprocessor).put(repVar, res);
			return res;
		} catch (ExecutionException e) {
      throw new CacheException(e);
    }
	}

	protected IRVar getRepVar() {
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
	
	@Override
	public Object getProperty(String name) {
		Preconditions.checkArgument(properties != null);
		return properties.get(name);
	}	
	
	@Override
	public Object setProperty(String name, Object o) {
		Preconditions.checkArgument(properties != null);
		return properties.put(name, o);
	}
}
