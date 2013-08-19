package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.Expression.Kind.VARIABLE;

import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ExecutionException;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.MapMaker;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.Sort;

import edu.nyu.cascade.prover.CacheException;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public class VariableExpressionImpl extends ExpressionImpl implements
    VariableExpression {
  private static final LoadingCache<ExpressionManagerImpl, ConcurrentMap<String, Expr>> varCache = CacheBuilder
      .newBuilder().build(
          new CacheLoader<ExpressionManagerImpl, ConcurrentMap<String, Expr>>(){
            public ConcurrentMap<String, Expr> load(ExpressionManagerImpl expressionManager) {
              return new MapMaker().makeMap();
            }
          });
  
  
  static VariableExpressionImpl valueOf(
      ExpressionManagerImpl exprManager, Expression e) {
    if (e instanceof VariableExpressionImpl) {
      return (VariableExpressionImpl) e;
    } else if (e instanceof VariableExpression) {
      VariableExpression e2 = (VariableExpression) e;
      return new VariableExpressionImpl(exprManager, e2.getName(), e2.getType(),
          false);
    } else if (e instanceof ExpressionImpl && e.isVariable()) {
      ExpressionImpl ei = (ExpressionImpl) e; 
      assert( exprManager.equals(ei.getExpressionManager()) );
      String name = ei.getZ3Expression().toString();
      return new VariableExpressionImpl(exprManager, name, ei.getType(), 
          false);
    } else {
      throw new IllegalArgumentException("Expression type: " + e.getClass());
    }
  }

  static ExpressionImpl valueOfVariable(
      ExpressionManagerImpl exprManager, final Expr expr, Type type) throws Z3Exception {
    Preconditions.checkArgument(expr.IsConst());
    Preconditions.checkArgument(exprManager.toType(expr.Sort()).equals( type ));

    VariableExpressionImpl result = new VariableExpressionImpl(exprManager,
        VARIABLE, expr, expr.toString(), type);
    result.setIsVariable(true);
    return result;
  }
  
  static ExpressionImpl valueOfVariable(
      ExpressionManagerImpl exprManager, final String str, Type type) throws Z3Exception {
    VariableExpressionImpl result = new VariableExpressionImpl(exprManager, str, type, false);
    result.setIsVariable(true);
    return result;
  }
  
  protected VariableExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      Expr expr, String name, Type type) {
    super(exprManager, kind, expr, type);
    setName(name);
  }
  
  protected VariableExpressionImpl(final ExpressionManagerImpl exprManager, String name, Type type, boolean fresh) {
    super(exprManager, new VariableConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, String name, Sort sort) {
        /* TODO: see if var is already defined. There's a bug in lookupVar
         * bc it's second parameter is a output parameter. Need to change
         * the API so that it only takes the name.
         */
        try {
          if(varCache.get(exprManager).containsKey(name)) {
            return varCache.get(exprManager).get(name);
          }
          
          StringBuilder sb = new StringBuilder().append(name);
          /** For variable name contains '#', wrap it in '||' */
          if(name.indexOf('#') >= 0)   sb.insert(0, '|').append('|');
          TheoremProverImpl.z3FileCommand("(declare-const " + sb.toString() + " " + sort + ")");
          TheoremProverImpl.debugCommand("(declare-const " + sb.toString() + " : " + sort + ")");
          Expr res = ctx.MkConst(name, sort);
          varCache.get(exprManager).put(name, res);
          return res;
        } catch (Z3Exception e) {
          throw new TheoremProverException(e);
        } catch (ExecutionException e) {
          throw new CacheException(e);
        }
      }
    }, name, type, fresh);
  }

  /** Constructor with strategy, for subclasses that need to modify the
   * interaction with Z3 (c.f., FunctionVariable).
   */
  protected VariableExpressionImpl(ExpressionManagerImpl exprManager,
      VariableConstructionStrategy strategy, String name,
      Type type, boolean fresh) {
    super(exprManager,strategy,name,type,fresh);
  }

  @Override
  public String getName() {
    return super.getName();
  }

}
