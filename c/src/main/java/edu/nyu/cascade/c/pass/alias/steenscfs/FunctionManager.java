package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.concurrent.ConcurrentMap;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.pass.alias.Function;
import xtc.type.FunctionT;
import xtc.type.Type;

public class FunctionManager {
	// FIXME: Function reload!
	final ConcurrentMap<String, Function<ECR>> functionCache = Maps
			.newConcurrentMap();

	final UnionFindECR uf;

	FunctionManager(UnionFindECR uf) {
		this.uf = uf;
	}

	Function<ECR> register(String funcName, Type funcType) {
		Preconditions.checkNotNull(funcName);
		Preconditions.checkArgument(!functionCache.containsKey(funcName));
		Preconditions.checkArgument(funcType.resolve().isFunction());

		String funcScope = CScopeAnalyzer.getRootScopeName();
		FunctionT funcTy = funcType.resolve().toFunction();
		Function<ECR> func = new Function<ECR>(funcName, funcScope, funcType);

		if (!funcTy.getResult().isVoid()) {
			ECR res = uf.createECR(funcTy.getResult());
			func.setResult(res);
		}

		functionCache.put(funcName, func);
		return func;
	}

	Function<ECR> get(String funcName) {
		Preconditions.checkNotNull(funcName);
		Preconditions.checkArgument(functionCache.containsKey(funcName));
		return functionCache.get(funcName);
	}

	boolean isRegistered(String funcName) {
		return functionCache.containsKey(funcName);
	}

	void reset() {
		functionCache.clear();
	}
}
