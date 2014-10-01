package edu.nyu.cascade.z3;

import static edu.nyu.cascade.prover.Expression.Kind.CONSTANT;
import static edu.nyu.cascade.prover.Expression.Kind.DIVIDE;
import static edu.nyu.cascade.prover.Expression.Kind.MINUS;
import static edu.nyu.cascade.prover.Expression.Kind.MULT;
import static edu.nyu.cascade.prover.Expression.Kind.PLUS;
import static edu.nyu.cascade.prover.Expression.Kind.POW;
import static edu.nyu.cascade.prover.Expression.Kind.UNARY_MINUS;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.RationalExpression;
import edu.nyu.cascade.prover.type.IntegerType;
import edu.nyu.cascade.prover.type.RationalType;
import edu.nyu.cascade.prover.type.Type;

final class RationalExpressionImpl extends ExpressionImpl implements
    RationalExpression {

  static RationalExpressionImpl mkConstant(ExpressionManagerImpl em,
      final int numerator, final int denominator) {
  	return new RationalExpressionImpl(em, CONSTANT,
        new NullaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx) throws Z3Exception {
        return ctx.mkReal(numerator, denominator);
      }
    });
  }

  static RationalExpressionImpl mkDivide(ExpressionManagerImpl exprManager,
      Expression numerator, Expression denominator) {
    Preconditions.checkArgument(isRatOrInt(numerator));
    Preconditions.checkArgument(isRatOrInt(denominator));
    return new RationalExpressionImpl(exprManager, DIVIDE,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right) 
          throws Z3Exception {
        return ctx.mkDiv((ArithExpr)left, (ArithExpr)right);
      }
    }, numerator, denominator);
  }

  static RationalExpressionImpl mkMinus(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new RationalExpressionImpl(exprManager, MINUS,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right)
          throws Z3Exception {
        return ctx.mkSub(new ArithExpr[]{(ArithExpr) left, (ArithExpr) right});
      }
    }, a, b);
  }

  static RationalExpressionImpl mkMult(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new RationalExpressionImpl(exprManager, MULT,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right)
          throws Z3Exception {
        return ctx.mkMul(new ArithExpr[]{(ArithExpr) left, (ArithExpr) right});
      }
    }, a, b);
  }

  static RationalExpressionImpl mkMult(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> terms) {
    Preconditions.checkArgument(!Iterables.isEmpty(terms));
    return new RationalExpressionImpl(exprManager, MULT,
        new NaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr[] args)
          throws Z3Exception {
        return ctx.mkMul((ArithExpr[]) args);
      }  
    }, terms);
  }

  static RationalExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
      Expression a, Expression b) {
    return new RationalExpressionImpl(exprManager, PLUS,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right)
          throws Z3Exception {
        return ctx.mkAdd(new ArithExpr[] {(ArithExpr) left, (ArithExpr) right});
      }
    }, a, b);
  }

  static RationalExpressionImpl mkPlus(ExpressionManagerImpl exprManager,
      Iterable<? extends Expression> args) {
    Preconditions.checkArgument(!Iterables.isEmpty(args));
    return new RationalExpressionImpl(exprManager, PLUS,
        new NaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr[] args)
          throws Z3Exception {
        return ctx.mkAdd((ArithExpr[]) args);
      }
    }, args);
  }

  static RationalExpressionImpl mkPow(ExpressionManagerImpl exprManager,
      Expression base, Expression exp) {
    return new RationalExpressionImpl(exprManager, POW,
        new BinaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left, Expr right)
          throws Z3Exception {
        return ctx.mkPower((ArithExpr)left, (ArithExpr)right);
      }
    }, base, exp);
  }

  static RationalExpressionImpl mkUminus(ExpressionManagerImpl exprManager,
      Expression a) {
    return new RationalExpressionImpl(exprManager, UNARY_MINUS,
        new UnaryConstructionStrategy() {
      @Override
      public Expr apply(Context ctx, Expr left) throws Z3Exception {
        return ctx.mkUnaryMinus((ArithExpr) left);
      }
    }, a);
  }

  private static <T extends Type> boolean isRatOrInt(Expression e) {
    Type t = e.getType();
    return ((Type) t instanceof RationalType || (Type) t instanceof IntegerType);
  }

  RationalExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      UnaryConstructionStrategy strategy, Expression a) {
    super(exprManager, kind, strategy, a);
  }

  RationalExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      NullaryConstructionStrategy strategy) {
    super(exprManager, kind, strategy);
    setType(exprManager.rationalType());
  }

  RationalExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      BinaryConstructionStrategy strategy, Expression left,
      Expression right) {
    super(exprManager, kind, strategy, left, right);
    setType(getExpressionManager().rationalType());
  }

  RationalExpressionImpl(ExpressionManagerImpl exprManager, Kind kind,
      NaryConstructionStrategy strategy, Iterable<? extends Expression> args) {
    super(exprManager, kind, strategy, args);
    setType(getExpressionManager().rationalType());
  }
  
  private RationalExpressionImpl(ExpressionManagerImpl em, Kind kind, 
      Expr expr, RationalType type, Iterable<? extends ExpressionImpl> children) {
  	super(em, kind, expr, type, children);
  }
  
  static RationalExpressionImpl create(ExpressionManagerImpl em, Kind kind, 
      Expr expr, Type type, Iterable<? extends ExpressionImpl> children) {
  	Preconditions.checkArgument(type.isRational());
    return new RationalExpressionImpl(em, kind, expr, type.asRational(), children);
  }

  static RationalExpressionImpl valueOf(
      ExpressionManagerImpl exprManager, Expression e) {
    if (e instanceof RationalExpressionImpl) {
      return (RationalExpressionImpl) e;
    } else {
      throw new IllegalArgumentException("RationalExpression.valueOf: " + e);
    }
  }
  
  @Override
  public RationalTypeImpl getType() {
  	return getExpressionManager().rationalType();
  }

  @Override
  public RationalExpressionImpl divide(Expression e) {
    return getType().divide(this, e);
  }

  @Override
  public BooleanExpressionImpl gt(Expression e) {
    return getType().gt(this, e);
  }

  @Override
  public BooleanExpressionImpl geq(Expression e) {
    return getType().geq(this, e);
  }

  @Override
  public BooleanExpressionImpl lt(Expression e) {
    return getType().lt(this, e);
  }

  @Override
  public BooleanExpressionImpl leq(Expression e) {
    return getType().leq(this, e);
  }

  @Override
  public RationalExpressionImpl mult(Expression e) {
    return getType().mult(this, e);
  }

  @Override
  public RationalExpressionImpl pow(Expression exp) {
    return getType().pow(this, exp);
  }

  @Override
  public RationalExpressionImpl minus(Expression e) {
    return getType().subtract(this, e);
  }

  @Override
  public RationalExpressionImpl plus(Expression e) {
    return getType().add(this, e);
  }
}
