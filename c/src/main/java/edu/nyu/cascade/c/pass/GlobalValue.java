package edu.nyu.cascade.c.pass;

import java.util.concurrent.ConcurrentMap;

import com.google.common.collect.Maps;

import edu.nyu.cascade.util.Pair;
import xtc.type.Type;

public class GlobalValue extends Value {

	static ConcurrentMap<Pair<String, String>, GlobalValue> GlobalMap = Maps.newConcurrentMap();
	
	GlobalValue(String name, String scope, Type type) {
		super(type);
		setName(name);
		setScope(scope);
	}
	
	/// Always create the fresh value - node is declarator
	static GlobalValue getOrCreate(String name, String scope, Type type) {
		if (GlobalMap.containsKey(Pair.of(name, scope))) 
			return GlobalMap.get(Pair.of(name, scope));
		
		GlobalValue GV = new GlobalValue(name, scope, type);
		GlobalMap.put(Pair.of(name, scope), GV);
		return GV;
	}

	public boolean isConstant() {
		// TODO Auto-generated method stub
		return false;
	}
}
