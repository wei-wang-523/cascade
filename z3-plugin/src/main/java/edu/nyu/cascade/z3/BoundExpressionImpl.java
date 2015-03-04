package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.Expression.Kind.BOUND;

import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ExecutionException;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.MapMaker;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.BoundExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.CacheException;

class BoundExpressionImpl extends ExpressionImpl implements BoundExpression {
  private static final LoadingCache<ExpressionManagerImpl, ConcurrentMap<String, Expr>> boundCache = CacheBuilder
      .newBuilder().build(
          new CacheLoader<ExpressionManagerImpl, ConcurrentMap<String, Expr>>(){
            public ConcurrentMap<String, Expr> load(ExpressionManagerImpl expressionManager) {
              return new MapMaker().makeMap();
            }
          });
	
  BoundExpressionImpl(final ExpressionManagerImpl exprManager, String name, final int index, Type type, boolean fresh)  {
  	super(exprManager, new BoundVariableConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, String name, Sort sort) throws Z3Exception {
        /* TODO: see if var is already defined. There's a bug in lookupVar
         * bc it's second parameter is a output parameter. Need to change
         * the API so that it only takes the name.
         */
        try {
          if(boundCache.get(exprManager).containsKey(name)) {
            return boundCache.get(exprManager).get(name);
          }
          Expr bound = ctx.mkBound(index, sort);
          boundCache.get(exprManager).put(name, bound);
          return bound;
        } catch (ExecutionException e) {
          throw new CacheException(e);
        }
      }
  	}, name, type, fresh);
  	setSymbol(exprManager);
  }
  
  BoundExpressionImpl(final ExpressionManagerImpl exprManager, String name, Type type, boolean fresh)  {
  	super(exprManager, new BoundVariableConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, String name, Sort sort) throws Z3Exception {
        /* TODO: see if var is already defined. There's a bug in lookupVar
         * bc it's second parameter is a output parameter. Need to change
         * the API so that it only takes the name.
         */
        try {
          if(boundCache.get(exprManager).containsKey(name)) {
            return boundCache.get(exprManager).get(name);
          }
          Expr bound = ctx.mkConst(name, sort);
          boundCache.get(exprManager).put(name, bound);
          return bound;
        } catch (ExecutionException e) {
          throw new CacheException(e);
        }
      }
  	}, name, type, fresh);
  }
  
  private BoundExpressionImpl(ExpressionManagerImpl exprManager,
      Expr expr, String name, Type type) {
    super(exprManager, BOUND, expr, type);
    setName(name);
  }
  
  static BoundExpressionImpl valueOfBound(
      ExpressionManagerImpl exprManager, Symbol symbol, Type type) {
  	Preconditions.checkNotNull(symbol);
    return new BoundExpressionImpl(exprManager, symbol.toString(), type, false);
  }
  
  static BoundExpressionImpl valueOf(
      ExpressionManagerImpl exprManager, Expression e) {
  	Preconditions.checkArgument(e instanceof BoundExpressionImpl
  			|| e instanceof BoundExpression);
    if (e instanceof BoundExpressionImpl) {
      return (BoundExpressionImpl) e;
    } 
    
    BoundExpression e2 = (BoundExpression) e;
    return new BoundExpressionImpl(exprManager, e2.getName(), e2.getType(),
    		false);
  }
  
	private Symbol symbol = null;
  
  Symbol getSymbol() {
  	return symbol;
  }
  
  private void setSymbol(ExpressionManagerImpl exprManager) {
  	try {
	    symbol = exprManager.getTheoremProver().getZ3Context().mkSymbol(getName());
    } catch (Z3Exception e) {
    	throw new TheoremProverException(e);
    }
  }
  
  @Override
  public String getName() {
  	return super.getName();
  }
}
