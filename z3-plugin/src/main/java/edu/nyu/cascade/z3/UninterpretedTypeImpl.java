package edu.nyu.cascade.z3;

import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ExecutionException;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.MapMaker;
import com.microsoft.z3.Expr;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
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

	static UninterpretedTypeImpl create(ExpressionManagerImpl em, String name) {
		try {
			if (typeCache.get(em).containsKey(name))
				return typeCache.get(em).get(name);
			else {
				UninterpretedTypeImpl res = new UninterpretedTypeImpl(em, name);
				typeCache.get(em).put(name, res);
				return res;
			}
		} catch (ExecutionException e) {
			throw new CacheException(e);
		}
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
			setZ3Type(exprManager.getTheoremProver().getZ3Context()
			    .mkUninterpretedSort(name));
			exprManager.addToTypeCache(this);

			TheoremProverImpl.z3FileCommand("(declare-sort " + name + " 0)");
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
	public UninterpretedBoundExpressionImpl boundVar(String name, boolean fresh) {
		return UninterpretedBoundExpressionImpl.create(getExpressionManager(), name,
		    this, fresh);
	}

	@Override
	public UninterpretedBoundExpressionImpl boundExpression(String name,
	    int index, boolean fresh) {
		return UninterpretedBoundExpressionImpl.create(getExpressionManager(), name,
		    index, this, fresh);
	}

	@Override
	public String toString() {
		return "UNINTERPRETED" + " OF " + name;
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public DomainType getDomainType() {
		return DomainType.UNINTERPRETED;
	}

	@Override
	protected UninterpretedExpressionImpl createExpression(Expr res,
	    Expression oldExpr, Iterable<? extends ExpressionImpl> children) {
		return UninterpretedExpressionImpl.create(getExpressionManager(), oldExpr
		    .getKind(), res, oldExpr.getType(), children);
	}
}
