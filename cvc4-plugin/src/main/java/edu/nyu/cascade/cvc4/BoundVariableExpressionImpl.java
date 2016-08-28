package edu.nyu.cascade.cvc4;

import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ExecutionException;

import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.MapMaker;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.DatatypeType;
import edu.nyu.cascade.prover.BoundExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.CacheException;

class BoundVariableExpressionImpl extends ExpressionImpl
		implements BoundExpression {
	static final LoadingCache<ExpressionManagerImpl, ConcurrentMap<String, Expr>> boundCache = CacheBuilder
			.newBuilder().build(
					new CacheLoader<ExpressionManagerImpl, ConcurrentMap<String, Expr>>() {
						public ConcurrentMap<String, Expr> load(
								ExpressionManagerImpl expressionManager) {
							return new MapMaker().makeMap();
						}
					});

	static BoundVariableExpressionImpl create(ExpressionManagerImpl exprManager,
			String name, Type type, boolean fresh) {
		return new BoundVariableExpressionImpl(exprManager, name, type, fresh);
	}

	BoundVariableExpressionImpl(final ExpressionManagerImpl exprManager,
			String name, Type type, boolean fresh) {
		super(exprManager, new BoundVariableConstructionStrategy() {
			@Override
			public Expr apply(ExprManager em, String name,
					edu.nyu.acsys.CVC4.Type type) {
				try {
					if (boundCache.get(exprManager).containsKey(name)) {
						return boundCache.get(exprManager).get(name);
					}

					Expr bound = em.mkBoundVar(name, type);
					boundCache.get(exprManager).put(name, bound);

					if (type.isDatatype()) {
						DatatypeType dtt = new DatatypeType(type);
						String dtName = dtt.getDatatype().getName();
						TheoremProverImpl.cvc4FileCommand("(declare-const ", bound,
								" " + dtName + ")");
					} else {
						TheoremProverImpl.cvc4FileCommand("(declare-const ", bound, type,
								")");
					}
					return bound;
				} catch (ExecutionException e) {
					throw new CacheException(e);
				}
			}
		}, name, type, fresh);
	}

	static BoundVariableExpressionImpl valueOf(ExpressionManagerImpl exprManager,
			Expression e) {
		if (e instanceof BoundVariableExpressionImpl) {
			return (BoundVariableExpressionImpl) e;
		} else if (e instanceof BoundExpression) {
			BoundExpression e2 = (BoundExpression) e;
			return new BoundVariableExpressionImpl(exprManager, e2.getName(),
					e2.getType(), false);
		} else if (e instanceof ExpressionImpl && e.isBound()) {
			ExpressionImpl ei = (ExpressionImpl) e;
			assert (exprManager.equals(ei.getExpressionManager()));
			Expr cvcExpr = ei.getCvc4Expression();
			String name = cvcExpr.toString();
			return new BoundVariableExpressionImpl(exprManager, name, ei.getType(),
					false);
		} else {
			throw new IllegalArgumentException("Expression type: " + e.getClass());
		}
	}

	@Override
	public String getName() {
		return super.getName();
	}
}
