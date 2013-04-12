package edu.nyu.cascade.ir.expr;

import java.util.Arrays;
import java.util.List;

import com.google.common.collect.Lists;
import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.TupleType;

public class PointerIntegerEncoding extends
    AbstractTypeEncoding<TupleExpression> implements
    IntegerEncoding<TupleExpression>, PointerEncoding<TupleExpression> {
  private static final String UNKNOWN_VARIABLE_NAME = "bv_encoding_unknown";
  private static final String CONST_VARIABLE_NAME = "const";
  private static TupleType type;
  private static BitVectorType elemType;
  
  public static PointerIntegerEncoding create(ExpressionManager exprManager, int size) {
    elemType = exprManager.bitVectorType(size);
    type = exprManager.tupleType("pointer", elemType, elemType);
    return new PointerIntegerEncoding(exprManager, type);
  }
  
  private PointerIntegerEncoding(ExpressionManager exprManager, TupleType type) {
    super(exprManager, type);
  }
  
  private boolean isConstant(BitVectorExpression expr) {
    return expr.isVariable() && 
        CONST_VARIABLE_NAME.equals(expr.asVariable().getName());
  }
  
  private BitVectorExpression chooseRef(BitVectorExpression lhs, BitVectorExpression rhs) {
    Preconditions.checkArgument(!(isConstant(lhs) && isConstant(rhs)));
    return isConstant(lhs) ? rhs : lhs;
  }
  
  private BitVectorExpression chooseRef(Iterable <? extends BitVectorExpression> refs) {
    BitVectorExpression res = null;
    for(BitVectorExpression ref : refs) {
      if(isConstant(ref)) continue;
      if(res == null) res = ref;
      else 
        throw new ExpressionFactoryException("Invalid pointer expression argument.");
    }
    return res;
  }
  
  private BitVectorType getElemType() {
    return elemType;
  }
  
  public TupleExpression castToPointer(BitVectorExpression expr) {
    BitVectorExpression lhsRes = getExpressionManager().variable(CONST_VARIABLE_NAME,
        getElemType(), false).asBitVector();
    return getExpressionManager().tuple(type, lhsRes, expr);
  }
  
  @Override
  public TupleExpression bitwiseAnd(TupleExpression lhs,
      TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_0 = lhs.index(0).asBitVector();
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_0 = rhs.index(0).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BitVectorExpression lhsRes = chooseRef(lhs_0, rhs_0);
    BitVectorExpression rhsRes = lhs_1.and(rhs_1);
    return getExpressionManager().tuple(type, lhsRes, rhsRes);
  }

  @Override
  public TupleExpression constant(int c) {
    BitVectorExpression lhsRes = getExpressionManager().variable(CONST_VARIABLE_NAME,
        getElemType(), false).asBitVector();
    BitVectorExpression rhsRes = getExpressionManager().bitVectorConstant(c, getElemType().getSize());
    return getExpressionManager().tuple(type, lhsRes, rhsRes);
  }

  @Override
  public TupleExpression decr(TupleExpression expr) {
    return minus(expr, one());
  }

  @Override
  public BooleanExpression distinct(
      Iterable<? extends TupleExpression> exprs) {
    return getExpressionManager().distinct(exprs);
  }

  @Override
  public TupleType getType() {
    return type;
  }
  
  @Override
  public BooleanExpression greaterThan(TupleExpression lhs,
      TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_0 = lhs.index(0).asBitVector();
    BitVectorExpression rhs_0 = rhs.index(0).asBitVector();
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BooleanExpression cond1 = lhs_0.eq(rhs_0);
    BooleanExpression cond2 = getExpressionManager().greaterThan(lhs_1, rhs_1);
    return cond1.and(cond2);
  }
  
  @Override
  public BooleanExpression signedGreaterThan(TupleExpression lhs,
      TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_0 = lhs.index(0).asBitVector();
    BitVectorExpression rhs_0 = rhs.index(0).asBitVector();
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BooleanExpression cond1 = lhs_0.eq(rhs_0);
    BooleanExpression cond2 = getExpressionManager().signedGreaterThan(lhs_1, rhs_1);
    return cond1.and(cond2);
  }
  
  @Override
  public BooleanExpression greaterThanOrEqual(TupleExpression lhs,
      TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_0 = lhs.index(0).asBitVector();
    BitVectorExpression rhs_0 = rhs.index(0).asBitVector();
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BooleanExpression cond1 = lhs_0.eq(rhs_0);
    BooleanExpression cond2 = getExpressionManager().greaterThanOrEqual(lhs_1, rhs_1);
    return cond1.and(cond2);
  }

  @Override
  public BooleanExpression signedGreaterThanOrEqual(TupleExpression lhs,
      TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);    
    BitVectorExpression lhs_0 = lhs.index(0).asBitVector();
    BitVectorExpression rhs_0 = rhs.index(0).asBitVector();
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BooleanExpression cond1 = lhs_0.eq(rhs_0);
    BooleanExpression cond2 = getExpressionManager().signedGreaterThanOrEqual(lhs_1, rhs_1);
    return cond1.and(cond2);
  }

  @Override
  public TupleExpression ifThenElse(BooleanExpression b,
      TupleExpression thenExpr, TupleExpression elseExpr) {
    return b.ifThenElse(thenExpr, elseExpr).asTuple();
  }

  @Override
  public TupleExpression incr(TupleExpression expr) {
    return plus(expr, one());
  }

  @Override
  public BooleanExpression lessThan(TupleExpression lhs,
      TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_0 = lhs.index(0).asBitVector();
    BitVectorExpression rhs_0 = rhs.index(0).asBitVector();
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BooleanExpression cond1 = lhs_0.eq(rhs_0);
    BooleanExpression cond2 = getExpressionManager().lessThan(lhs_1, rhs_1);
    return cond1.and(cond2);
  }
  
  @Override
  public BooleanExpression signedLessThan(TupleExpression lhs,
      TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_0 = lhs.index(0).asBitVector();
    BitVectorExpression rhs_0 = rhs.index(0).asBitVector();
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BooleanExpression cond1 = lhs_0.eq(rhs_0);
    BooleanExpression cond2 = getExpressionManager().signedLessThan(lhs_1, rhs_1);
    return cond1.and(cond2);
  }

  @Override
  public BooleanExpression lessThanOrEqual(TupleExpression lhs,
      TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_0 = lhs.index(0).asBitVector();
    BitVectorExpression rhs_0 = rhs.index(0).asBitVector();
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BooleanExpression cond1 = lhs_0.eq(rhs_0);
    BooleanExpression cond2 = getExpressionManager().lessThanOrEqual(lhs_1, rhs_1);
    return cond1.and(cond2);
  }
  
  @Override
  public BooleanExpression signedLessThanOrEqual(TupleExpression lhs,
      TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_0 = lhs.index(0).asBitVector();
    BitVectorExpression rhs_0 = rhs.index(0).asBitVector();
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BooleanExpression cond1 = lhs_0.eq(rhs_0);
    BooleanExpression cond2 = getExpressionManager().signedLessThanOrEqual(lhs_1, rhs_1);
    return cond1.and(cond2);
  }

  @Override
  public TupleExpression minus(TupleExpression lhs,
      TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_0 = lhs.index(0).asBitVector();
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_0 = rhs.index(0).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BitVectorExpression lhsRes = chooseRef(lhs_0, rhs_0);
    BitVectorExpression rhsRes = lhs_1.minus(rhs_1);
    return getExpressionManager().tuple(type, lhsRes, rhsRes);
  }

  private TupleExpression not(TupleExpression expr) {
    Preconditions.checkArgument(expr.size() == 2);
    BitVectorExpression lhsRes = expr.index(0).asBitVector();
    BitVectorExpression rhsRes = expr.index(1).asBitVector().not();
    return getExpressionManager().tuple(type, lhsRes, rhsRes);
  }

  @Override
  public TupleExpression negate(TupleExpression expr) {
    return incr(not(expr));
  }

  @Override
  public TupleExpression ofBoolean(BooleanExpression b) {
    return b.ifThenElse(one(), zero()).asTuple();
  }

  @Override
  public TupleExpression one() {
    return constant(1);
  }

  @Override
  public TupleExpression plus(Iterable<? extends TupleExpression> args) {
    List<BitVectorExpression> lhsList = Lists.newArrayList();
    List<BitVectorExpression> rhsList = Lists.newArrayList();
    for(TupleExpression arg : args) {
      Preconditions.checkArgument(arg.size() == 2);
      lhsList.add(arg.index(0).asBitVector());
      rhsList.add(arg.index(1).asBitVector());
    }
    Expression lhsRes = chooseRef(lhsList);
    Expression rhsRes = getExpressionManager().bitVectorPlus(
        getElemType().getSize(), rhsList);
    return getExpressionManager().tuple(type, lhsRes, rhsRes);
  }

  @Override
  public TupleExpression plus(TupleExpression... args) {
    return plus(Arrays.asList(args));
  }

  @Override
  public TupleExpression plus(TupleExpression lhs,
      TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_0 = lhs.index(0).asBitVector();
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_0 = rhs.index(0).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BitVectorExpression lhsRes = chooseRef(lhs_0, rhs_0);
    BitVectorExpression rhsRes = lhs_1.plus(getElemType().getSize(), rhs_1);
    return getExpressionManager().tuple(type, lhsRes, rhsRes);
  }

  @Override
  public TupleExpression times(TupleExpression lhs,
      TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_0 = lhs.index(0).asBitVector();
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_0 = rhs.index(0).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BitVectorExpression lhsRes = chooseRef(lhs_0, rhs_0);
    BitVectorExpression rhsRes = lhs_1.times(getElemType().getSize(), rhs_1);
    return getExpressionManager().tuple(type, lhsRes, rhsRes);
  }
  
  @Override
  public TupleExpression divide(TupleExpression lhs,
      TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_0 = lhs.index(0).asBitVector();
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_0 = rhs.index(0).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BitVectorExpression lhsRes = chooseRef(lhs_0, rhs_0);
    BitVectorExpression rhsRes = lhs_1.divides(rhs_1);
    return getExpressionManager().tuple(type, lhsRes, rhsRes);
  }
  
  @Override
  public TupleExpression mod(TupleExpression lhs,
      TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_0 = lhs.index(0).asBitVector();
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_0 = rhs.index(0).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BitVectorExpression lhsRes = chooseRef(lhs_0, rhs_0);
    BitVectorExpression rhsRes = lhs_1.signedRems(rhs_1);
    return getExpressionManager().tuple(type, lhsRes, rhsRes);
  }
  
  @Override
  public BooleanExpression toBoolean(TupleExpression expr) {
    return neq(expr, zero());
  }

  @Override
  public TupleExpression unknown() {
    return variable(UNKNOWN_VARIABLE_NAME, true);
  }

  @Override
  public TupleExpression zero() {
    return constant(0);
  }

  @Override
  public TupleExpression ofExpression(Expression x) {
    Preconditions.checkArgument(x.isTuple());
    return x.asTuple();
  }

  @Override
  public Expression index(TupleExpression x, int i) {
    Preconditions.checkArgument(x.size() == 2);
    Preconditions.checkArgument(i==0 || i==1);
    return x.index(i);
  }

  @Override
  public TupleExpression update(TupleExpression x, int index, Expression val) {
    Preconditions.checkArgument(x.size() == 2);
    Preconditions.checkArgument(index==0 || index==1);
    Preconditions.checkArgument(val.getType().equals(x.getType().getElementTypes().get(1)));
    return x.update(index, val);
  }

  @Override
  public BooleanExpression neq(TupleExpression lhs, TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_0 = lhs.index(0).asBitVector();
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_0 = rhs.index(0).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    return getExpressionManager().or(lhs_0.neq(rhs_0), lhs_1.neq(rhs_1));
  }
}
