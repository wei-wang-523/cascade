package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.util.concurrent.ConcurrentMap;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.CScopeAnalyzer;
import xtc.type.FunctionT;
import xtc.type.Type;

public class CFSFunctionManager {
	// FIXME: Function reload!
	final ConcurrentMap<String, CFSFunction> functionCache = Maps
			.newConcurrentMap();

	final ECREncoder ecrEncoder;

	CFSFunctionManager(ECREncoder ecrEncoder) {
		this.ecrEncoder = ecrEncoder;
	}

	CFSFunction register(String funcName, Type funcType) {
		Preconditions.checkNotNull(funcName);
		Preconditions.checkArgument(!functionCache.containsKey(funcName));
		Preconditions.checkArgument(funcType.resolve().isFunction());

		String funcScope = CScopeAnalyzer.getRootScopeName();
		FunctionT funcTy = funcType.resolve().toFunction();
		CFSFunction func = new CFSFunction(funcName, funcScope, funcType);

		if (!funcTy.getResult().isVoid()) {
			ECR res = ecrEncoder.createECR(funcTy.getResult());
			func.setResult(res);
		}

		functionCache.put(funcName, func);
		return func;
	}

	CFSFunction get(String funcName) {
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
