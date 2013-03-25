package edu.nyu.cascade.cvc4;

import static edu.nyu.cascade.prover.Expression.Kind.CONSTANT;
import static edu.nyu.cascade.prover.Expression.Kind.MINUS;
import static edu.nyu.cascade.prover.Expression.Kind.MULT;
import static edu.nyu.cascade.prover.Expression.Kind.PLUS;
import static edu.nyu.cascade.prover.Expression.Kind.DIVIDE;
import static edu.nyu.cascade.prover.Expression.Kind.POW;
import static edu.nyu.cascade.prover.Expression.Kind.UNARY_MINUS;
import static edu.nyu.cascade.prover.Expression.Kind.MOD;

import java.util.List;
import java.util.concurrent.ConcurrentMap;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.MapMaker;

import edu.nyu.acsys.CVC4.Exception;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Rational;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.IntegerExpression;
import edu.nyu.cascade.prover.RationalExpression;

public final class IntegerExpressionImpl extends ExpressionImpl implements
    IntegerExpression {
  private static final ConcurrentMap<ExpressionManagerImpl, ConcurrentMap<Integer, IntegerExpressionImpl>> constantCache = new MapMaker()
      .makeComputingMap(new Function<ExpressionManagerImpl, ConcurrentMap<Integer, IntegerExpressionImpl>>() {
        @Override
        public ConcurrentMap<Integer, IntegerExpressionImpl> apply(
            final ExpressionManagerImpl exprManager) {
          return new MapMaker()
              .makeComputingMap(new Function<Integer, IntegerExpressionImpl>() {
                @Override
                public IntegerExpressionImpl apply(Integer value) {
                  return new IntegerExpressionImpl(exprManager, value);
                }
              });
        }
      });

  static IntegerExpressionImpl mkConstant(ExpressionManagerImpl em, long c) {
    return constantCache.get(em).get(c);
  }
  
  static IntegerExpressionImpl mkConstant(ExpressionManagerImpl em, int c) {
    return constantCache.get(em).get(c);
  }

  static IntegerExpressionImpl mkMinus(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new IntegerExpressionImpl(exprManager, MINUS,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr left, Expr right)
              throws Exception {
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.MINUS, left, right);
          }
        }, a, b);
  }

  static IntegerExpressionImpl mkMult(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new IntegerExpressionImpl(exprManager, MULT,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr left, Expr right)
              throws Exception {
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.MULT, left, right);
          }
        }, a, b);
  }
  
  static IntegerExpressionImpl mkDivide(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new IntegerExpressionImpl(exprManager, DIVIDE,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr left, Expr right)
              throws Exception { // support divides by zero
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.INTS_DIVISION_TOTAL, left, right);
          }
      }, a, b);
  }
  
  static IntegerExpressionImpl mkModulous(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new IntegerExpressionImpl(exprManager, MOD, 
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(ExprManager em, Expr left, Expr right)
          throws Exception { // support modulus by zero
        return em.mkExpr(edu.nyu.acsys.CVC4.Kind.INTS_MODULUS_TOTAL, left, right);
      }
    }, a, b);
  }

  static IntegerExpressionImpl mkMult(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> terms) {
    Preconditions.checkArgument(!Iterables.isEmpty(terms));
    return new IntegerExpressionImpl(exprManager, MULT,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, List<Expr> args)
              throws Exception {
            Expr result = null;
            for (Expr arg : args) {
              if (result == null) {
                result = arg;
              } else {
                result = em.mkExpr(edu.nyu.acsys.CVC4.Kind.MULT, result, arg);
              }
            }
            return result;
          }

        }, terms);
  }

  static IntegerExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new IntegerExpressionImpl(exprManager, PLUS,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr left, Expr right)
              throws Exception {
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.PLUS, left, right);
          }
        }, a, b);
  }

  static IntegerExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> args) {
    Preconditions.checkArgument(!Iterables.isEmpty(args));
    return new IntegerExpressionImpl(exprManager, PLUS,
        new NaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, List<Expr> args)
              throws Exception {
            Expr result = null;
            for(Expr arg : args) {
              if (result == null) {
                result = arg;
              } else {
                result = em.mkExpr(edu.nyu.acsys.CVC4.Kind.PLUS, result, arg);
              }
            }
            return result;
          }
        }, args);
  }

  static IntegerExpressionImpl mkPow(ExpressionManagerImpl exprManager,
      Expression base, Expression exp) {
    return new IntegerExpressionImpl(exprManager, POW,
        new BinaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr left, Expr right)
              throws Exception {
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.POW, left, right);
          }
        }, base, exp);
  }

  static IntegerExpressionImpl mkUminus(ExpressionManagerImpl exprManager,
      Expression a) {
    return new IntegerExpressionImpl(exprManager, UNARY_MINUS,
        new UnaryConstructionStrategy() {
          @Override
          public Expr apply(ExprManager em, Expr left) throws Exception {
            return em.mkExpr(edu.nyu.acsys.CVC4.Kind.UMINUS, left);
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

  private IntegerExpressionImpl(ExpressionManagerImpl em, int value) {
    super(em, CONSTANT, em.integerType());
    ExprManager cvc4_em = em.getTheoremProver().getCvc4ExprManager();
    setCvc4Expression(cvc4_em.mkConst(new Rational(value)));
    setConstant(true);
  }

  private IntegerExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinaryConstructionStrategy strategy, Expression a, Expression b) {
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

  @Override
  public RationalExpression castToRational() {
    // return getType().castToRational(this);
    throw new UnsupportedOperationException();
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