package edu.nyu.cascade.c.pass;

import java.util.concurrent.ConcurrentMap;
import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.util.Pair;
import xtc.type.Type;

public class GlobalVariable extends GlobalObject {
	static final ConcurrentMap<Pair<String, String>, GlobalVariable> globalVarCache = Maps
			.newConcurrentMap();

	protected GlobalVariable(String name, String scope, Type type) {
		super(name, scope, type);
	}

	static GlobalVariable getOrCreate(String varName, String varScope,
			Type varTy) {
		Pair<String, String> varKey = Pair.of(varName, varScope);
		if (globalVarCache.containsKey(varKey)) {
			return globalVarCache.get(varKey);
		} else {
			GlobalVariable var = new GlobalVariable(varName, varScope, varTy);
			globalVarCache.put(varKey, var);
			return var;
		}
	}

	static GlobalVariable get(String varName, String varScope) {
		Preconditions.checkArgument(globalVarCache.containsKey(Pair.of(varName,
				varScope)));
		return globalVarCache.get(Pair.of(varName, varScope));
	}
}
