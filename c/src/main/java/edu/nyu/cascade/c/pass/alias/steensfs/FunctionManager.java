package edu.nyu.cascade.c.pass.alias.steensfs;

import java.util.concurrent.ConcurrentMap;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.pass.alias.Function;
import xtc.type.FunctionT;
import xtc.type.Type;

public class FunctionManager {
	// FIXME: Function<ECR> reload!
	final ConcurrentMap<String, Function<ECR>> FunctionCache = Maps
			.newConcurrentMap();

	final UnionFindECR uf;

	FunctionManager(UnionFindECR uf) {
		this.uf = uf;
	}

	Function<ECR> register(String funcName, Type funcType) {
		Preconditions.checkNotNull(funcName);
		Preconditions.checkArgument(!FunctionCache.containsKey(funcName));
		Preconditions.checkArgument(funcType.resolve().isFunction());

		String funcScope = CScopeAnalyzer.getRootScopeName();
		FunctionT funcTy = funcType.resolve().toFunction();
		Function<ECR> func = new Function<ECR>(funcName, funcScope, funcType);

		if (!funcTy.getResult().isVoid()) {
			ECR res = ECR.create(BlankType
					.blank(Size.createForType(funcTy.getResult()), Parent.getBottom()));
			func.setResult(res);
		}

		FunctionCache.put(funcName, func);
		return func;
	}

	Function<ECR> get(String funcName) {
		Preconditions.checkNotNull(funcName);
		Preconditions.checkArgument(FunctionCache.containsKey(funcName));
		return FunctionCache.get(funcName);
	}

	boolean isRegistered(String funcName) {
		return FunctionCache.containsKey(funcName);
	}

	void reset() {
		FunctionCache.clear();
	}
}
