package edu.nyu.cascade.ir.expr;

import java.math.BigInteger;
import java.util.Arrays;

import xtc.type.C;
import xtc.type.NumberT;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Preferences;

public class BitVectorIntegerEncoding extends
    AbstractTypeEncoding<BitVectorExpression> implements
    IntegerEncoding<BitVectorExpression> {
  private static final String UNKNOWN_VARIABLE_NAME = "bv_encoding_unknown";
  
  private final int INT_SIZE, LONG_SIZE, LONGLONG_SIZE;
  
  private final int WORD_SIZE;
  
  private final C cAnalyzer;
  
  public static BitVectorIntegerEncoding create(ExpressionManager exprManager, C cAnalyzer, int wordSize) {
    BitVectorType type = exprManager.bitVectorType(wordSize);
    return new BitVectorIntegerEncoding(exprManager, type, cAnalyzer);
  }
  
  private BitVectorIntegerEncoding(ExpressionManager exprManager, BitVectorType type, C _cAnalyzer) {
    super(exprManager, type);
    cAnalyzer = _cAnalyzer;
  	if(Preferences.isSet(Preferences.OPTION_MULTI_CELL)) {
  		INT_SIZE = (int) cAnalyzer.getSize(NumberT.INT);
  		LONG_SIZE = (int) cAnalyzer.getSize(NumberT.LONG);
  		LONGLONG_SIZE = (int) cAnalyzer.getSize(NumberT.LONG_LONG);
  	} else {
  		INT_SIZE = 1; LONG_SIZE = 1; LONGLONG_SIZE = 1;
  	}
  	WORD_SIZE = type.getSize();
  }
  
  protected C getCAnalyzer() {
  	return cAnalyzer;
  }
  
  protected int getWordSize() {
  	return WORD_SIZE;
  }
  
  @Override
  public BitVectorExpression bitwiseAnd(BitVectorExpression a,
      BitVectorExpression b) {
    return a.and(b);
  }
  
  @Override
  public BitVectorExpression constant(int c) {
    return getExpressionManager().bitVectorConstant(c, INT_SIZE * WORD_SIZE);
  }
  
  @Override
  public BitVectorExpression constant(long c) {
  	return getExpressionManager().bitVectorConstant(c, LONG_SIZE * WORD_SIZE);
  }
  
  @Override
  public BitVectorExpression constant(BigInteger c) {
  	ExpressionManager exprManager = getExpressionManager();
  	int cSize = c.bitLength();
  	if(cSize > LONGLONG_SIZE * WORD_SIZE)
  		throw new IllegalArgumentException("Constant is too large to be supported " + c.toString());
  	else if(cSize > LONG_SIZE * WORD_SIZE)
  		return exprManager.bitVectorConstant(c, LONGLONG_SIZE * WORD_SIZE);
  	else if(cSize > INT_SIZE * WORD_SIZE)
  		return exprManager.bitVectorConstant(c, LONG_SIZE * WORD_SIZE);
  	else
  		return exprManager.bitVectorConstant(c, INT_SIZE * WORD_SIZE);
  }

  @Override
  public BitVectorExpression decr(BitVectorExpression expr) {
    return expr.minus(one());
  }

  @Override
	public BitVectorExpression incr(BitVectorExpression expr) {
  	int size = expr.getSize();
	  return expr.plus(size, one());
	}

	@Override
  public BooleanExpression distinct(
      Iterable<? extends BitVectorExpression> exprs) {
    return getExpressionManager().distinct(exprs);
  }

  @Override
  public BitVectorType getType() {
    return super.getType().asBitVectorType();
  }
  
  @Override
  public BooleanExpression greaterThan(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().greaterThan(lhs, rhs);
  }
  
  @Override
  public BooleanExpression signedGreaterThan(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().signedGreaterThan(lhs, rhs);
  }
  
  @Override
  public BooleanExpression greaterThanOrEqual(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().greaterThanOrEqual(lhs, rhs);
  }

  @Override
  public BooleanExpression signedGreaterThanOrEqual(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().signedGreaterThanOrEqual(lhs, rhs);
  }

  @Override
  public BitVectorExpression ifThenElse(BooleanExpression b,
      BitVectorExpression thenExpr, BitVectorExpression elseExpr) {
    return b.ifThenElse(thenExpr, elseExpr).asBitVector();
  }

  @Override
  public BooleanExpression lessThan(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().lessThan(lhs, rhs);
  }
  
  @Override
  public BooleanExpression signedLessThan(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().signedLessThan(lhs, rhs);
  }

  @Override
  public BooleanExpression lessThanOrEqual(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().lessThanOrEqual(lhs, rhs);
  }
  
  @Override
  public BooleanExpression signedLessThanOrEqual(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().signedLessThanOrEqual(lhs, rhs);
  }

  @Override
  public BitVectorExpression minus(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return getExpressionManager().bitVectorMinus(lhs, rhs);
  }

  @Override
  public BitVectorExpression negate(BitVectorExpression arg) {
    return incr(arg.not());
  }

  @Override
  public BooleanExpression neq(BitVectorExpression lhs, BitVectorExpression rhs) {
    return lhs.neq(rhs);
  }

  @Override
  public BitVectorExpression ofBoolean(BooleanExpression b) {
    return b.ifThenElse(one(), zero()).asBitVector();
  }
  
  @Override
  public BitVectorExpression ofInteger(BitVectorExpression bv, int size) {
  	int srcSize = bv.getSize();
  	if(srcSize == size)	return bv;
  	
  	if(srcSize < size)	
  		return bv.signExtend(size);
  	else
  		return bv.extract(size-1, 0);
  }

  @Override
  public BitVectorExpression plus(Iterable<? extends BitVectorExpression> args) {
  	int maxSize = 0;
  	for(BitVectorExpression arg : args) {
  		maxSize = Math.max(maxSize, arg.getSize());
  	}
    return getExpressionManager().bitVectorPlus(maxSize, args);
  }

  @Override
  public BitVectorExpression plus(BitVectorExpression... args) {
    return plus(Arrays.asList(args));
  }

  @Override
  public BitVectorExpression plus(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    int size = Math.max(lhs.getSize(), rhs.getSize());
    return lhs.plus(size, rhs);
  }

  @Override
  public BitVectorExpression times(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    int size = Math.max(lhs.getSize(), rhs.getSize());
    return lhs.times(size, rhs);
  }
  
  @Override
  public BitVectorExpression divide(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.divides(rhs);
  }
  
  @Override
  public BitVectorExpression mod(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.signedRems(rhs);
  }
  
  @Override
  public BooleanExpression toBoolean(BitVectorExpression expr) {
    int size = expr.getType().getSize();
    Expression zero = getExpressionManager().bitVectorZero(size);
    return expr.neq(zero);
  }

  @Override
  public BitVectorExpression unknown() {
    return variable(UNKNOWN_VARIABLE_NAME, true);
  }
  
  @Override
  public BitVectorExpression unknown(Type type) {
    Preconditions.checkArgument(type.isBitVectorType());
    return type.asBitVectorType().variable(UNKNOWN_VARIABLE_NAME, true);
  }

  @Override
	public BitVectorExpression one() {
	  return constant(1);
	}

	@Override
  public BitVectorExpression zero() {
    return constant(0);
  }

  @Override
  public BitVectorExpression ofExpression(Expression x) {
    Preconditions.checkArgument(x.isBitVector());
    return x.asBitVector();
  }
  
  @Override
  public boolean isEncodingFor(Expression x) {
    return x.getType().isBitVectorType();
  }
  
  @Override
  public BitVectorExpression lshift(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.lshift(rhs);
  }
  
  @Override
  public BitVectorExpression rshift(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.rshift(rhs);
  }
  
  @Override
  public BitVectorExpression signedDivide(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.signedDivides(rhs);
  }
  
  @Override
  public BitVectorExpression rem(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.rems(rhs);
  }
  
  @Override
  public BitVectorExpression signedRem(BitVectorExpression lhs,
      BitVectorExpression rhs) {
    return lhs.signedRems(rhs);
  }

	@Override
	public BitVectorExpression uminus(BitVectorExpression expr) {
		return expr.uminus();
	}
	
  @Override
  public BooleanExpression eq(BitVectorExpression lhs, BitVectorExpression rhs) {
  	if(lhs.getSize() > rhs.getSize()) rhs = rhs.signExtend(lhs.getSize());
  	if(lhs.getSize() < rhs.getSize()) lhs = lhs.signExtend(rhs.getSize());
    return lhs.eq((Expression)rhs);
  }
  
  @Override
  public BitVectorExpression variable(String name, Type type, boolean fresh) {
  	Preconditions.checkArgument(type.isBitVectorType());
  	return type.asBitVectorType().variable(name, fresh);
  }
}
