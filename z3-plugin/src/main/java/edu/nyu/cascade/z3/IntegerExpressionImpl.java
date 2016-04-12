package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.Expression.Kind.CONSTANT;
import static edu.nyu.cascade.prover.Expression.Kind.MINUS;
import static edu.nyu.cascade.prover.Expression.Kind.MULT;
import static edu.nyu.cascade.prover.Expression.Kind.PLUS;
import static edu.nyu.cascade.prover.Expression.Kind.DIVIDE;
import static edu.nyu.cascade.prover.Expression.Kind.POW;
import static edu.nyu.cascade.prover.Expression.Kind.UNARY_MINUS;
import static edu.nyu.cascade.prover.Expression.Kind.MOD;

import java.math.BigInteger;
import java.util.Collections;
import java.util.concurrent.ExecutionException;

import com.google.common.base.Preconditions;
import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.Context;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.IntegerType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.CacheException;

final class IntegerExpressionImpl extends ExpressionImpl implements
    IntegerExpression {
  
	static final LoadingCache<ExpressionManagerImpl, LoadingCache<BigInteger, IntegerExpressionImpl>> constantCache = CacheBuilder
      .newBuilder().build(
          new CacheLoader<ExpressionManagerImpl, LoadingCache<BigInteger, IntegerExpressionImpl>>(){
            public LoadingCache<BigInteger, IntegerExpressionImpl> load(final ExpressionManagerImpl exprManager) {
              return CacheBuilder.newBuilder().build(new CacheLoader<BigInteger, IntegerExpressionImpl>(){
                public IntegerExpressionImpl load(BigInteger value) {
                  return new IntegerExpressionImpl(exprManager, value);
                }
              });
            }
          });

  static IntegerExpressionImpl mkConstant(ExpressionManagerImpl em, long value) {
    try {
      return constantCache.get(em).get(BigInteger.valueOf(value));
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  static IntegerExpressionImpl mkConstant(ExpressionManagerImpl em, int value) {
    try {
      return constantCache.get(em).get(BigInteger.valueOf((long) value));
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  static IntegerExpressionImpl mkConstant(ExpressionManagerImpl em, BigInteger value) {
    try {
      return constantCache.get(em).get(value);
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }

  static IntegerExpressionImpl mkMinus(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new IntegerExpressionImpl(exprManager, MINUS,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) {
        try {
          return ctx.mkSub(new ArithExpr[]{(ArithExpr) left, (ArithExpr) right});
        } catch (Z3Exception e) {
          throw new TheoremProverException(e);
        }
      }
     }, a, b);
  }

  static IntegerExpressionImpl mkMult(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new IntegerExpressionImpl(exprManager, MULT,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) {
        try {
          return ctx.mkMul(new ArithExpr[]{(ArithExpr) left, (ArithExpr) right});
        } catch (Z3Exception e) {
          throw new TheoremProverException(e);
        }
      }
    }, a, b);
  }
  
  static IntegerExpressionImpl mkDivide(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new IntegerExpressionImpl(exprManager, DIVIDE,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) {
        try {
          return ctx.mkDiv((ArithExpr) left, (ArithExpr) right);
        } catch (Z3Exception e) {
          throw new TheoremProverException(e);
        }
      }
    }, a, b);
  }
  
  static IntegerExpressionImpl mkModulous(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new IntegerExpressionImpl(exprManager, MOD, 
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) {
        try {
          return ctx.mkMod((IntExpr) left, (IntExpr) right);
        } catch (Z3Exception e) {
          throw new TheoremProverException(e);
        }
      }
    }, a, b);
  }

  static IntegerExpressionImpl mkMult(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> terms) {
    Preconditions.checkArgument(!Iterables.isEmpty(terms));
    return new IntegerExpressionImpl(exprManager, MULT,
        new NaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr[] args) {
        try {
          return ctx.mkMul((IntExpr[]) args);
        } catch (Z3Exception e) {
          throw new TheoremProverException(e);
        }
      }
    }, terms);
  }

  static IntegerExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new IntegerExpressionImpl(exprManager, PLUS,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) {
        try {
          return ctx.mkAdd(new ArithExpr[]{(ArithExpr)left, (ArithExpr)right});
        } catch (Z3Exception e) {
          throw new TheoremProverException(e);
        }
      }
    }, a, b);
  }

  static IntegerExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
      Expression first, Expression... rest) {
    return mkPlus(exprManager, Lists.asList(first, rest));
  }

  static IntegerExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> args) {
    Preconditions.checkArgument(!Iterables.isEmpty(args));
    return new IntegerExpressionImpl(exprManager, PLUS,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(Context ctx, Expr[] args) {
            try {
            return ctx.mkAdd((ArithExpr[]) args);
            } catch (Z3Exception e) {
              throw new TheoremProverException(e);
            }
          }
    }, args);
  }

  static IntegerExpressionImpl mkPow(ExpressionManagerImpl exprManager,
      Expression base, Expression exp) {
    return new IntegerExpressionImpl(exprManager, POW,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) {
        try {
          return ctx.mkPower((ArithExpr) left, (ArithExpr) right);
        } catch (Z3Exception e) {
          throw new TheoremProverException(e);
        }
      }
    }, base, exp);
  }

  static IntegerExpressionImpl mkUminus(ExpressionManagerImpl exprManager,
      Expression a) {
    return new IntegerExpressionImpl(exprManager, UNARY_MINUS,
        new UnaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left) {
        try {
          return ctx.mkUnaryMinus((ArithExpr) left);
        } catch (Z3Exception e) {
          throw new TheoremProverException(e);
        }
      }
    }, a);
  }

  static IntegerExpressionImpl valueOf(ExpressionManagerImpl exprManager,
      ExpressionImpl e) {
    if( exprManager.equals( e.getExpressionManager() ) ) {
      if (e instanceof IntegerExpressionImpl) {
        return (IntegerExpressionImpl) e;
      } else {
        return new IntegerExpressionImpl((ExpressionImpl) e);
      }
    }
    
    switch( e.getKind() ) {
    default:
      throw new UnsupportedOperationException("Unexpected kind: " + e + " {"
          + e.getKind() + "}");
    }
  }

  /** Copy constructor */
  private IntegerExpressionImpl(ExpressionImpl e) {
    super(e);
  }

  private IntegerExpressionImpl(ExpressionManagerImpl em, BigInteger value) {
    super(em, CONSTANT, em.integerType());
    try {
      setZ3Expression(em.getTheoremProver().getZ3Context().mkInt(value.toString()));
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
  }

  private IntegerExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinaryConstructionStrategy strategy, Expression a, Expression b) 
          {
    super(exprManager, kind, strategy, a, b);
    setType(getExpressionManager().integerType());
  }

  private IntegerExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      NaryConstructionStrategy strategy,
      Iterable<? extends Expression> args) {
    super(exprManager, kind, strategy, args);
    setType(getExpressionManager().integerType());
  }

  private IntegerExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      UnaryConstructionStrategy strategy, Expression a) {
    super(exprManager, kind, strategy, a);
    setType(getExpressionManager().integerType());
  }
  
  private IntegerExpressionImpl(ExpressionManagerImpl em, Kind kind, 
      Expr expr, IntegerType type, Iterable<? extends ExpressionImpl> children) {
  	super(em, kind, expr, type, children);
  }
  
  static IntegerExpressionImpl create(ExpressionManagerImpl em, Kind kind, 
      Expr expr, Type type, Iterable<? extends ExpressionImpl> children) {
  	Preconditions.checkArgument(type.isInteger());
    return new IntegerExpressionImpl(em, kind, expr, type.asInteger(), children);
  }

  @Override
  public IntegerTypeImpl getType() {
    return (IntegerTypeImpl) super.getType();
  }

  @Override
  public BooleanExpressionImpl greaterThan(Expression e) {
    return BooleanExpressionImpl.mkGt(getExpressionManager(), this, e);
  }

  @Override
  public BooleanExpressionImpl greaterThanOrEqual(Expression e) {
    return BooleanExpressionImpl.mkGeq(getExpressionManager(), this, e);
  }

  @Override
  public BooleanExpressionImpl lessThan(Expression e) {
    return BooleanExpressionImpl.mkLt(getExpressionManager(), this, e);
  }

  @Override
  public BooleanExpressionImpl lessThanOrEqual(Expression e) {
    return BooleanExpressionImpl.mkEq(getExpressionManager(), this, e);
  }

  @Override
  public IntegerExpression minus(Expression e) {
    return mkMinus(getExpressionManager(), this, e);
  }

  @Override
  public IntegerExpression negate() {
    return mkUminus(getExpressionManager(), this);

  }

  @Override
  public IntegerExpression plus(Expression e) {
    return mkPlus(getExpressionManager(), this, e);
  }

  @Override
	public IntegerExpression plus(IntegerExpression... rest) {
		return mkPlus(getExpressionManager(), this, rest);
	}

	@Override
	public IntegerExpression plus(Iterable<? extends IntegerExpression> rest) {
		return mkPlus(getExpressionManager(), 
				Iterables.concat(Collections.singletonList(this), rest));
	}

	@Override
  public IntegerExpression pow(Expression e) {
    return mkPow(getExpressionManager(), this, e);
  }

  @Override
  public IntegerExpression times(Expression e) {
    return mkMult(getExpressionManager(), this, e);
  }

  @Override
  public IntegerExpression divides(Expression e) {
    return mkDivide(getExpressionManager(), this, e);
  }
  
  @Override
  public IntegerExpression mods(Expression e) {
    return mkModulous(getExpressionManager(), this, e);
  } 
}
