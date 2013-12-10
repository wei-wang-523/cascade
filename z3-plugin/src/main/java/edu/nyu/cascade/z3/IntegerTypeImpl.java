package edu.nyu.cascade.z3;

import java.util.concurrent.ExecutionException;

import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.Lists;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Z3Exception;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.IntegerType;
import edu.nyu.cascade.util.CacheException;

public class IntegerTypeImpl extends TypeImpl implements IntegerType {
  
  private static final LoadingCache<ExpressionManagerImpl, IntegerTypeImpl> typeCache = CacheBuilder
      .newBuilder().build(
          new CacheLoader<ExpressionManagerImpl, IntegerTypeImpl>(){
            public IntegerTypeImpl load(ExpressionManagerImpl expressionManager) {
              return new IntegerTypeImpl(expressionManager);
            }
          });

  public static IntegerTypeImpl getInstance(ExpressionManagerImpl expressionManager) {
    try {
      return typeCache.get(expressionManager);
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }
  
  protected IntegerTypeImpl(ExpressionManagerImpl expressionManager) {
    super(expressionManager);
    try {
      setZ3Type(expressionManager.getTheoremProver().getZ3Context().IntSort());
    } catch (Z3Exception e) {
      throw new TheoremProverException(e);
    }
  }

  protected IntegerTypeImpl(ExpressionManagerImpl expressionManager,
      BinaryConstructionStrategy strategy, Expression expr1,
      Expression expr2) {
    super(expressionManager, strategy, expr1, expr2);
  }

  protected IntegerTypeImpl(ExpressionManagerImpl em, UnaryConstructionStrategy strategy,
      Expression expr) {
    super(em, strategy, expr);
  }

  @Override
  public IntegerExpressionImpl add(
      Expression a,
      Expression b) {
    return IntegerExpressionImpl.mkPlus(getExpressionManager(),a, b);
  }
  
  @Override
  public IntegerExpressionImpl add(
      Expression first,
      Expression... rest) {
    return IntegerExpressionImpl.mkPlus(getExpressionManager(),Lists.asList(first, rest));
  }

  @Override
  public IntegerExpressionImpl add(
      Iterable<? extends Expression> addends) {
    return IntegerExpressionImpl.mkPlus(getExpressionManager(),addends);
  }

  @Override
  public IntegerExpressionImpl divide(Expression a,
      Expression b) {
    return IntegerExpressionImpl.mkDivide(getExpressionManager(), a, b);
  }

  @Override
  public IntegerExpressionImpl mod(Expression a,
      Expression b) {
    return IntegerExpressionImpl.mkModulous(getExpressionManager(), a, b);
  }

  @Override
  public BooleanExpressionImpl geq(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkGeq(getExpressionManager(),a, b);  
    }
  
  @Override
  public BooleanExpressionImpl sgeq(Expression a,
      Expression b) {
    throw new UnsupportedOperationException();
  }
  
  @Override
  public DomainType getDomainType() {
    return DomainType.INTEGER;
  }


  @Override
  public String getName() {
    return "INT";
  }

  @Override
  public BooleanExpressionImpl gt(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkGt(getExpressionManager(),a, b);  
  }
  
  @Override
  public BooleanExpression sgt(Expression a, 
      Expression b) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanExpressionImpl leq(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkLeq(getExpressionManager(),a, b);
  }
  
  @Override
  public BooleanExpression sleq(Expression a, 
      Expression b) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanExpressionImpl lt(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkLt(getExpressionManager(),a, b);
  }

  @Override
  public BooleanExpression slt(Expression a, Expression b) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }
  
  @Override
  public IntegerExpressionImpl mult(
      Expression left,
      Expression right) {
    return IntegerExpressionImpl.mkMult(getExpressionManager(),left,right);
  }

  @Override
  public IntegerExpressionImpl mult(
      Iterable<? extends Expression> terms) {
    return IntegerExpressionImpl.mkMult(getExpressionManager(),terms);
  }

  @Override
  public IntegerExpressionImpl negate(Expression a) {
    return IntegerExpressionImpl.mkUminus(getExpressionManager(),a);
  }

  @Override
  public IntegerExpressionImpl one() {
    return IntegerExpressionImpl.mkConstant(getExpressionManager(),1);
  }

  @Override
  public IntegerExpressionImpl pow(Expression base,
      Expression exp) {
    return IntegerExpressionImpl.mkPow(getExpressionManager(),base,exp);
  }

  @Override
  public IntegerExpressionImpl subtract(
      Expression a,
      Expression b) {
    return IntegerExpressionImpl.mkMinus(getExpressionManager(),a, b);
  }

  @Override
  TypeImpl subType(ExpressionManagerImpl exprManager, Expr expr) {
    throw new UnsupportedOperationException("Records not supported by Z3 yet (sorry!)");
  }

  @Override
  public IntegerVariableImpl variable(String name, boolean fresh) {
    return new IntegerVariableImpl(getExpressionManager(), name, this, fresh);
  }

  @Override
  public IntegerExpressionImpl zero() {
    return IntegerExpressionImpl.mkConstant(getExpressionManager(),0);
  }

  @Override
  public IntegerVariableImpl boundVariable(String name, boolean fresh) {
    throw new UnsupportedOperationException("bound variable is not supported in z3.");
  }
}
