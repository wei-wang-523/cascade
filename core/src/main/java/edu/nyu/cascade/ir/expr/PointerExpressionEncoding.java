package edu.nyu.cascade.ir.expr;

/** An expression factory that encodes memory as an int-to-int array. */

import java.util.Arrays;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.util.RecursionStrategies;
import edu.nyu.cascade.util.RecursionStrategies.UnaryRecursionStrategy;

public class PointerExpressionEncoding
    extends
    AbstractExpressionEncoding {

  protected final PointerEncoding<? extends Expression> pointerEncoding;

  public static PointerExpressionEncoding create(
      ExpressionManager exprManager,
      int size) throws ExpressionFactoryException
  {
    IntegerEncoding<BitVectorExpression> integerEncoding = BitVectorIntegerEncoding.create(exprManager,size);
    BooleanEncoding<BooleanExpression> booleanEncoding = new DefaultBooleanEncoding(exprManager);
    ArrayEncoding<ArrayExpression> arrayEncoding = new UnimplementedArrayEncoding<ArrayExpression>();
    PointerEncoding<TupleExpression> pointerEncoding = PointerIntegerEncoding.create(exprManager, size);
    return new PointerExpressionEncoding(integerEncoding,booleanEncoding,arrayEncoding,pointerEncoding);
  }
  
  private PointerExpressionEncoding(
      IntegerEncoding<BitVectorExpression> integerEncoding,
      BooleanEncoding<BooleanExpression> booleanEncoding,
      ArrayEncoding<ArrayExpression> arrayEncoding,
      PointerEncoding<TupleExpression> pointerEncoding)
  {
    super(integerEncoding,booleanEncoding,arrayEncoding);
    this.pointerEncoding = pointerEncoding;
  }
  
  public PointerEncoding<?> getPointerEncoding() {
    return pointerEncoding;
  }
  
  private PointerIntegerEncoding getPointerIntegerEncoding() {
    Preconditions.checkState(pointerEncoding instanceof PointerIntegerEncoding);
    return (PointerIntegerEncoding) pointerEncoding;
  }
  
  public Expression castToPointer(Expression expr) {
    Preconditions.checkArgument(expr.isBitVector());
    return getPointerIntegerEncoding().castToPointer(expr.asBitVector());
  }
  
  @Override
  public Expression castToBoolean(Expression expr) {
    if(expr.isTuple())
      return getPointerIntegerEncoding().eq(expr.asTuple(), zero().asTuple());
    else
      return super.castToBoolean(expr);
  }
  
  @Override
  public Expression castToInteger(Expression expr) {
    Expression res = expr;
    if(expr.isTuple()) {
      if(expr.getArity() == 2 
          && expr.getChild(0).isBitVector() && expr.getChild(1).isBitVector())
        res = getExpressionManager().tuple(((PointerIntegerEncoding)pointerEncoding).getType(),
            castToInteger(expr.asTuple().index(0)), castToInteger(expr.asTuple().index(1)));
    } else {
      res = super.castToInteger(expr);
    }
    return res;
  }
  
  @Override
  public Expression bitwiseAnd(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isTuple() && rhs.isTuple());
    return getPointerIntegerEncoding().bitwiseAnd(lhs.asTuple(), rhs.asTuple());
  }
  
  @Override
  public Expression integerConstant(int c) {
    return getPointerIntegerEncoding().constant(c);
  }
  
  @Override
  public Expression decr(Expression expr) {
    Preconditions.checkArgument(expr.isTuple());
    return getPointerIntegerEncoding().decr(expr.asTuple());
  }
  
  @Override
  public Expression divide(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isTuple() && rhs.isTuple());
    return getPointerIntegerEncoding().divide(lhs.asTuple(), rhs.asTuple());
  }
  
  @Override
  public BooleanExpression greaterThan(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isTuple() && rhs.isTuple());
    return getPointerIntegerEncoding().greaterThan(lhs.asTuple(), rhs.asTuple());
  }
  
  @Override
  public BooleanExpression greaterThanOrEqual(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isTuple() && rhs.isTuple());
    return getPointerIntegerEncoding().greaterThanOrEqual(lhs.asTuple(), rhs.asTuple());
  }
  
  @Override
  public Expression incr(Expression expr) {
    Preconditions.checkArgument(expr.isTuple());
    return getPointerIntegerEncoding().incr(expr.asTuple());
  }
  
  public Expression indexTuple(Expression expr, int index) {
    Preconditions.checkArgument(expr.isTuple());
    return getPointerIntegerEncoding().index(expr.asTuple(), index);
  }
  
  @Override
  public BooleanExpression lessThan(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isTuple() && rhs.isTuple());
    return getPointerIntegerEncoding().lessThan(lhs.asTuple(), rhs.asTuple());
  }
  
  @Override
  public BooleanExpression lessThanOrEqual(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isTuple() && rhs.isTuple());
    return getPointerIntegerEncoding().lessThanOrEqual(lhs.asTuple(), rhs.asTuple());
  }
  
  @Override
  public Expression minus(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isTuple() && rhs.isTuple());
    return getPointerIntegerEncoding().minus(lhs.asTuple(), rhs.asTuple());
  }
  
  @Override
  public Expression negate(Expression expr) {
    Preconditions.checkArgument(expr.isTuple());
    return getPointerIntegerEncoding().negate(expr.asTuple());
  }
  
  @Override
  public BooleanExpression neq(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isTuple() && rhs.isTuple());
    return getPointerIntegerEncoding().neq(lhs.asTuple(), rhs.asTuple());
  }
  
  @Override
  public Expression one() {
    return getPointerIntegerEncoding().one();
  }
  
  @Override
  public Expression plus(Iterable<? extends Expression> exprs) {
//    List<TupleExpression> tupleExprs = Lists.newArrayList();
//    for(Expression expr : exprs) {
//      Preconditions.checkArgument(expr.isTuple());
//      tupleExprs.add(expr.asTuple());
//    }
//    return getPointerIntegerEncoding().plus(tupleExprs);
    return getPointerIntegerEncoding().plus(
        RecursionStrategies.unaryRecursionOverList(exprs,
        new UnaryRecursionStrategy<Expression, TupleExpression>() {
      @Override
      public TupleExpression apply(Expression e) {
        Preconditions.checkArgument(e.isTuple());
        return e.asTuple();
      }
    }));
  }
  
  @Override
  public Expression plus(Expression... args)
  {
    return plus(Arrays.asList(args));
  }
  
  @Override
  public Expression plus(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isTuple() && rhs.isTuple());
    return getPointerIntegerEncoding().plus(lhs.asTuple(), rhs.asTuple());
  }
  
  @Override
  public Expression mod(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isTuple() && rhs.isTuple());
    return getPointerIntegerEncoding().mod(lhs.asTuple(), rhs.asTuple());
  }
  
  @Override
  public BooleanExpression signedGreaterThan(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isTuple() && rhs.isTuple());
    return getPointerIntegerEncoding().signedGreaterThan(lhs.asTuple(), rhs.asTuple());
  }
  
  @Override
  public BooleanExpression signedGreaterThanOrEqual(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isTuple() && rhs.isTuple());
    return getPointerIntegerEncoding().signedGreaterThanOrEqual(lhs.asTuple(), rhs.asTuple());
  }
  
  
  @Override
  public BooleanExpression signedLessThan(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isTuple() && rhs.isTuple());
    return getPointerIntegerEncoding().signedLessThan(lhs.asTuple(), rhs.asTuple());
  }
  
  @Override
  public BooleanExpression signedLessThanOrEqual(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isTuple() && rhs.isTuple());
    return getPointerIntegerEncoding().signedLessThanOrEqual(lhs.asTuple(), rhs.asTuple());
  }
  
  @Override
  public Expression times(Expression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.isTuple() && rhs.isTuple());
    return getPointerIntegerEncoding().times(lhs.asTuple(), rhs.asTuple());
  }
  
  @Override
  public BooleanExpression toBoolean(Expression expr) {
    Preconditions.checkArgument(expr.isTuple());
    return getPointerIntegerEncoding().toBoolean(expr.asTuple());
  }
  
  @Override
  public Expression unknown() {
    return getPointerIntegerEncoding().unknown();
  }
  
  public Expression updateTuple(Expression expr, int index, Expression val) {
    Preconditions.checkArgument(expr.isTuple());
    return getPointerIntegerEncoding().update(expr.asTuple(), index, val);
  }
  
  @Override
  public Expression zero() {
    return getPointerIntegerEncoding().zero();
  }
}
