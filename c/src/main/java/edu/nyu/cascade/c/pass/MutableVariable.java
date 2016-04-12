package edu.nyu.cascade.c.pass;

import java.util.concurrent.ConcurrentMap;
import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.util.Pair;
import xtc.type.Type;

public class MutableVariable extends MutableValue {

	static final ConcurrentMap<Pair<String, String>, MutableVariable> mutableCache = Maps.newConcurrentMap();

	protected MutableVariable(String name, String scope, Type type) {
		super(type);
		setName(name);
		setScope(scope);
	}

	static MutableVariable getOrCreate(String varName, String varScope, Type varTy) {
		Pair<String, String> varKey = Pair.of(varName, varScope);
		if(mutableCache.containsKey(varKey)) {
			return mutableCache.get(varKey);
		} else {
			MutableVariable var = new MutableVariable(varName, varScope, varTy);
			mutableCache.put(varKey, var);
			return var;
		}
	}
	
	static MutableVariable get(String varName, String varScope) {
		Preconditions.checkArgument(mutableCache.containsKey(Pair.of(varName, varScope)));
		return mutableCache.get(Pair.of(varName, varScope));
	}
}
