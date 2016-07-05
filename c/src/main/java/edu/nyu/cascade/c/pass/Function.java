package edu.nyu.cascade.c.pass;

import java.util.concurrent.ConcurrentMap;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Maps;

import xtc.Constants;
import xtc.type.Type;

public class Function extends GlobalObject {
	// FIXME: Function reload!
	static final ConcurrentMap<String, Function> functionCache = Maps
			.newConcurrentMap();

	Value Args[];

	private Function(String funcID, String funcScope, Type funcType) {
		super(funcID, funcScope, funcType);

		int paramSize = funcType.resolve().toFunction().getParameters().size();
		Args = new Value[paramSize];
	}

	public Iterable<Value> getArguments() {
		return ImmutableList.copyOf(Args);
	}

	static Function getOrCreate(String funcName, String funcScope, Type funcTy) {
		if (functionCache.containsKey(funcName)) {
			return functionCache.get(funcName);
		} else {
			Function func = new Function(funcName, funcScope, funcTy);
			functionCache.put(funcName, func);
			return func;
		}
	}

	static Function get(String funcName) {
		Preconditions.checkNotNull(funcName);
		Preconditions.checkArgument(functionCache.containsKey(funcName));
		return functionCache.get(funcName);
	}

	public boolean isDeclaration() {
		return !getType().hasAttribute(Constants.ATT_DEFINED);
	}

}
