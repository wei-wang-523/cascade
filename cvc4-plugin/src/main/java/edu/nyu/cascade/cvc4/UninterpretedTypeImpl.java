package edu.nyu.cascade.cvc4;

import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ExecutionException;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.MapMaker;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.Expression.Kind;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.prover.type.UninterpretedType;
import edu.nyu.cascade.util.CacheException;

final class UninterpretedTypeImpl extends TypeImpl implements
		UninterpretedType {
	private final String name;

	static final LoadingCache<ExpressionManagerImpl, ConcurrentMap<String, UninterpretedTypeImpl>> typeCache = CacheBuilder
			.newBuilder().build(
					new CacheLoader<ExpressionManagerImpl, ConcurrentMap<String, UninterpretedTypeImpl>>() {
						public ConcurrentMap<String, UninterpretedTypeImpl> load(
								ExpressionManagerImpl expressionManager) {
							return new MapMaker().makeMap();
						}
					});

	static UninterpretedTypeImpl create(ExpressionManagerImpl exprManager,
			String name) {
		try {
			if (typeCache.get(exprManager).containsKey(name))
				return typeCache.get(exprManager).get(name);
			else {
				UninterpretedTypeImpl res = new UninterpretedTypeImpl(exprManager,
						name);
				typeCache.get(exprManager).put(name, res);
				return res;
			}
		} catch (ExecutionException e) {
			throw new CacheException(e);
		}
	}

	@Override
	UninterpretedExpressionImpl createExpression(Expr res, Expression e,
			Kind kind, Iterable<ExpressionImpl> children) {
		Preconditions.checkArgument(e.isUninterpreted());
		return UninterpretedExpressionImpl.create(getExpressionManager(), kind, res,
				e.getType().asUninterpreted(), children);
	}

	static UninterpretedTypeImpl valueOf(ExpressionManagerImpl exprManager,
			Type type) {
		Preconditions.checkArgument(type.isUninterpreted());
		if (type instanceof UninterpretedTypeImpl) {
			return (UninterpretedTypeImpl) type;
		} else {
			UninterpretedType uninterType = type.asUninterpreted();
			return create(exprManager, uninterType.getName());
		}
	}

	private UninterpretedTypeImpl(ExpressionManagerImpl exprManager,
			String name) {
		super(exprManager);
		this.name = name;
		try {
			setCVC4Type(exprManager.getTheoremProver().getCvc4ExprManager().mkSort(
					name));
			TheoremProverImpl.cvc4FileCommand("(declare-sort " + name + " 0)");
		} catch (Exception e) {
			throw new TheoremProverException(e);
		}
	}

	@Override
	public UninterpretedVariableImpl variable(String name, boolean fresh) {
		return UninterpretedVariableImpl.create(getExpressionManager(), name, this,
				fresh);
	}

	@Override
	public UninterpretedBoundVariableImpl boundVar(String name, boolean fresh) {
		return UninterpretedBoundVariableImpl.create(getExpressionManager(), name,
				this, fresh);
	}

	@Override
	public UninterpretedBoundVariableImpl boundExpression(String name, int index,
			boolean fresh) {
		return boundVar(name, fresh);
	}

	@Override
	public String toString() {
		return "UNINTERPRETED " + " OF " + name;
	}

	@Override
	public String getName() {
		return toString();
	}

	@Override
	public DomainType getDomainType() {
		return DomainType.UNINTERPRETED;
	}
}
