package edu.nyu.cascade.z3;

import java.math.BigInteger;
import java.util.concurrent.ExecutionException;

import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ComputationException;
import com.microsoft.z3.Expr;

import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TheoremProverException;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.CacheException;

final class BitVectorTypeImpl extends TypeImpl implements BitVectorType {  
  private static final LoadingCache<ExpressionManagerImpl, LoadingCache<Integer, BitVectorTypeImpl>> cache = CacheBuilder
      .newBuilder().build(
          new CacheLoader<ExpressionManagerImpl, LoadingCache<Integer, BitVectorTypeImpl>>(){
            public LoadingCache<Integer, BitVectorTypeImpl> load(final ExpressionManagerImpl exprManager) {
              return CacheBuilder.newBuilder().build(new CacheLoader<Integer, BitVectorTypeImpl>(){
                public BitVectorTypeImpl load(Integer size) {
                  try {
                    return new BitVectorTypeImpl(exprManager, size);
                  } catch (TheoremProverException e) {
                    throw new ComputationException(e);
                  }
                }
              });
            }
          });  

  static BitVectorTypeImpl create(ExpressionManagerImpl exprManager, int size) {
    try {
      return cache.get(exprManager).get(size);
    } catch (ExecutionException e) {
      throw new CacheException(e);
    }
  }

  static BitVectorTypeImpl valueOf(ExpressionManagerImpl exprManager, Type t) {
    if( t instanceof BitVectorTypeImpl ) {
      return (BitVectorTypeImpl) t;
    } else {
      return create(exprManager, ((BitVectorType)t).getSize());
    }
  }
  
  private final int size;

  private BitVectorTypeImpl(ExpressionManagerImpl expressionManager, int size) {
    super(expressionManager);
    this.size = size;

    try {
      setZ3Type(expressionManager
          .getTheoremProver().getZ3Context().mkBitVecSort(size));
    } catch (Exception e) {
      throw new TheoremProverException(e);
    }
  }

  @Override
  public BitVectorExpressionImpl add(int size, Expression first,
      Expression... rest) {
  	ExpressionManagerImpl em = getExpressionManager();
  	BitVectorExpressionImpl sum = BitVectorExpressionImpl.mkPlus(em, first, rest);
  	return BitVectorExpressionImpl.typeConversion(em, size, sum);
  }

  @Override
  public BitVectorExpressionImpl add(int size, Expression a,
      Expression b) {
  	ExpressionManagerImpl em = getExpressionManager();
  	BitVectorExpressionImpl sum = BitVectorExpressionImpl.mkPlus(em, a, b);
  	return BitVectorExpressionImpl.typeConversion(em, size, sum);
  }

  @Override
  public BitVectorExpressionImpl add(int size, Iterable<? extends Expression> args) {  	
  	ExpressionManagerImpl em = getExpressionManager();
  	BitVectorExpressionImpl sum = BitVectorExpressionImpl.mkPlus(em, args);
  	return BitVectorExpressionImpl.typeConversion(em, size, sum);
  }

  @Override
  public BitVectorExpressionImpl bitwiseAnd(Expression a,
      Expression b) {
    return BitVectorExpressionImpl.mkAnd(getExpressionManager(), a, b);
  }
  
  @Override
  public BitVectorExpressionImpl bitwiseNand(Expression a,
      Expression b) {
    return BitVectorExpressionImpl.mkNand(getExpressionManager(), a, b);
  }

  @Override
  public BitVectorExpressionImpl bitwiseNor(Expression a,
      Expression b) {
    return BitVectorExpressionImpl.mkNor(getExpressionManager(), a, b);
  }

  @Override
  public BitVectorExpressionImpl bitwiseNot(Expression a) {
    return BitVectorExpressionImpl.mkNot(getExpressionManager(), a);
  }

  @Override
  public BitVectorExpressionImpl bitwiseOr(Expression a,
      Expression b) {
    return BitVectorExpressionImpl.mkOr(getExpressionManager(), a, b);
  }

  @Override
  public BitVectorExpressionImpl bitwiseXnor(Expression a,
      Expression b) {
    return BitVectorExpressionImpl.mkXnor(getExpressionManager(), a, b);
  }

  @Override
  public BitVectorExpressionImpl bitwiseXor(Expression a,
      Expression b) {
    return BitVectorExpressionImpl.mkXor(getExpressionManager(), a, b);
  }

  @Override
  public BitVectorExpressionImpl concat(Expression a,
      Expression b) {
    return BitVectorExpressionImpl.mkConcat(getExpressionManager(), a, b);
  }

  @Override
  public BitVectorExpressionImpl constant(int size, int val) {
    return BitVectorExpressionImpl.mkConstant(getExpressionManager(), size, val);
  }

  @Override
  public BitVectorExpressionImpl constant(int c) {
    return BitVectorExpressionImpl.mkConstant(getExpressionManager(), size, c);
  }
  
  @Override
  public BitVectorExpressionImpl constant(long c) {
    return BitVectorExpressionImpl.mkConstant(getExpressionManager(), size, c);
  }
  
  @Override
  public BitVectorExpressionImpl constant(BigInteger c) {
    return BitVectorExpressionImpl.mkConstant(getExpressionManager(), size, c);
  }

  @Override
  public BitVectorExpressionImpl extract(Expression a, int high, int low) {
    return BitVectorExpressionImpl.mkExtract(getExpressionManager(), a, high, low);
  }

  @Override
  public BooleanExpressionImpl geq(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkBvGeq(getExpressionManager(), a, b);
  }
  
  @Override
  public BooleanExpressionImpl sgeq(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkBvSGeq(getExpressionManager(), a, b);
  }

  @Override
  public DomainType getDomainType() {
    return DomainType.BITVECTOR;
  }

  @Override
  public String getName() {
    return toString();
  }

  @Override
  public int getSize() {
    return size;
  }

  @Override
  public BooleanExpressionImpl gt(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkBvGt(getExpressionManager(), a, b);
  }
  
  @Override
  public BooleanExpressionImpl sgt(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkBvSGt(getExpressionManager(), a, b);
  }

  @Override
  public BooleanExpressionImpl leq(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkBvLeq(getExpressionManager(), a, b);
  }
  
  @Override
  public BooleanExpressionImpl sleq(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkBvSLeq(getExpressionManager(), a, b);
  }

  @Override
  public BooleanExpressionImpl lt(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkBvLt(getExpressionManager(), a, b);
  }
  
  @Override
  public BooleanExpressionImpl slt(Expression a,
      Expression b) {
    return BooleanExpressionImpl.mkBvSLt(getExpressionManager(), a, b);
  }

  @Override
  public BitVectorExpression mult(int size, Expression a,
      Expression b) {
  	ExpressionManagerImpl em = getExpressionManager();
  	BitVectorExpressionImpl product = BitVectorExpressionImpl.mkMult(em, a, b);
  	return BitVectorExpressionImpl.typeConversion(em, size, product);
  }

  @Override
	public BitVectorExpression mult(int size, Expression first,
			Expression... rest) {
  	ExpressionManagerImpl em = getExpressionManager();
  	BitVectorExpressionImpl product = BitVectorExpressionImpl.mkMult(em, first, rest);
  	return BitVectorExpressionImpl.typeConversion(em, size, product);
	}

	@Override
	public BitVectorExpression mult(int size, Iterable<? extends Expression> args) {
		ExpressionManagerImpl em = getExpressionManager();
  	BitVectorExpressionImpl product = BitVectorExpressionImpl.mkMult(em, args);
  	return BitVectorExpressionImpl.typeConversion(em, size, product);
	}

	@Override
  public BitVectorExpression subtract(Expression a,
      Expression b) {
    return BitVectorExpressionImpl.mkMinus(
    		getExpressionManager(), a, b);
  }
  
  @Override
  public BitVectorExpression lshift(Expression a,
      Expression b) {
    return BitVectorExpressionImpl.mkLShift(getExpressionManager(), a, b);
  }
  
  @Override
  public BitVectorExpression rshift(Expression a,
      Expression b) {
    return BitVectorExpressionImpl.mkRShift(getExpressionManager(), a, b);
  }
  
  @Override
  public BitVectorExpression signedRshift(Expression a,
      Expression b) {
    return BitVectorExpressionImpl.mkSRShift(getExpressionManager(), a, b);
  }

  @Override
  public String toString() {
    return "BITVECTOR(" + size + ")";
  }

  @Override
  public BitVectorExpression variable(String name, boolean fresh) {
    return BitVectorVariableImpl.create(getExpressionManager(), name, this, fresh);
  }

  @Override
  public BitVectorExpression zero(int size) {
    return constant(size,0);
  }

  @Override
  public BitVectorBoundExpressionImpl boundVar(String name, boolean fresh) {
    return BitVectorBoundExpressionImpl.create(getExpressionManager(), name, this, fresh);
  }
  
  @Override
  public BitVectorBoundExpressionImpl boundExpression(String name, int index, boolean fresh) {
    return BitVectorBoundExpressionImpl.create(getExpressionManager(), name, index, this, fresh);
  }

	@Override
	public BitVectorExpression constant(int size, long val) {
		return BitVectorExpressionImpl.mkConstant(getExpressionManager(), size, val);
	}

	@Override
	public BitVectorExpression constant(int size, BigInteger val) {
		return BitVectorExpressionImpl.mkConstant(getExpressionManager(), size, val);
	}

	@Override
  public BitVectorExpression signedDivide(Expression a, Expression b) {
	  return BitVectorExpressionImpl.mkSDivide(getExpressionManager(), a, b);
  }

	@Override
  public BitVectorExpression rem(Expression a, Expression b) {
	  return BitVectorExpressionImpl.mkRem(getExpressionManager(), a, b);
  }

	@Override
  public BitVectorExpression signedRem(Expression a, Expression b) {
		return BitVectorExpressionImpl.mkSRem(getExpressionManager(), a, b);
  }

	@Override
  public BitVectorExpression signedExtend(int size, Expression bv) {
	  return BitVectorExpressionImpl.mkSignExtend(getExpressionManager(), size, bv);
  }

	@Override
  public BitVectorExpression zeroExtend(int size, Expression bv) {
	  return BitVectorExpressionImpl.mkZeroExtend(getExpressionManager(), size, bv);
  }

	@Override
	BitVectorExpressionImpl createExpression(Expr res, Expression oldExpr,
			Iterable<? extends ExpressionImpl> children) {
		return BitVectorExpressionImpl.create(getExpressionManager(), 
				oldExpr.getKind(), res, oldExpr.getType(), children);
	}
}
