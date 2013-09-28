package edu.nyu.cascade.ir.expr;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.base.Function;
import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.BitVectorExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.prover.type.UninterpretedType;
import edu.nyu.cascade.util.EqualsUtil;
import edu.nyu.cascade.util.HashCodeUtil;
import edu.nyu.cascade.util.Identifiers;

public class PointerEncoding implements TupleEncoding<TupleExpression> {
  private static final String UNKNOWN_VARIABLE_NAME = "bv_encoding_unknown";
  private static final String REF_TYPE_NAME = Identifiers.toValidId("refType");
  private static final String NULL_PTR_NAME = Identifiers.toValidId("nullRef");
  private static final String PTR_TYPE_NAME = Identifiers.toValidId("ptrType");
  private final TupleType type;
  private final UninterpretedType refType;
  private final BitVectorType offType;
  private final TupleExpression nullPtr;
  
  private final ExpressionManager exprManager;
  
  public static PointerEncoding create(ExpressionManager exprManager, int size) {
    return new PointerEncoding(exprManager, size);
  }
  
  private PointerEncoding(ExpressionManager exprManager, int size) {
    this.exprManager = exprManager;
    refType = exprManager.uninterpretedType(REF_TYPE_NAME);
    offType = exprManager.bitVectorType(size);
    type = exprManager.tupleType(PTR_TYPE_NAME, refType, offType);
    nullPtr = exprManager.tuple(type, exprManager.variable(NULL_PTR_NAME, refType, false),
        exprManager.bitVectorConstant(0, offType.getSize()));
  }
  
  protected TupleType getType() {
    return type;
  }
  
  protected TupleExpression getNullPtr() {
    return nullPtr;
  }
  
  @Override
  public TupleExpression decr(TupleExpression expr) {
    return minus(expr, getExpressionManager().bitVectorConstant(offType.getSize(), 1));
  }
  
  @Override
  public BooleanExpression greaterThan(TupleExpression lhs, TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BooleanExpression cond1 = lhs.index(0).eq(rhs.index(0));
    BooleanExpression cond2 = getExpressionManager().greaterThan(lhs_1, rhs_1);
    return cond1.and(cond2);
  }
  
  @Override
  public BooleanExpression greaterThanOrEqual(TupleExpression lhs, TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BooleanExpression cond1 = lhs.index(0).eq(rhs.index(0));
    BooleanExpression cond2 = getExpressionManager().greaterThanOrEqual(lhs_1, rhs_1);
    return cond1.and(cond2);
  }
  
  @Override
  public BooleanExpression lessThan(TupleExpression lhs, TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BooleanExpression cond1 = lhs.index(0).eq(rhs.index(0));
    BooleanExpression cond2 = getExpressionManager().lessThan(lhs_1, rhs_1);
    return cond1.and(cond2);
  }

  @Override
  public BooleanExpression lessThanOrEqual(TupleExpression lhs, TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    BooleanExpression cond1 = lhs.index(0).eq(rhs.index(0));
    BooleanExpression cond2 = getExpressionManager().lessThanOrEqual(lhs_1, rhs_1);
    return cond1.and(cond2);
  }
  
  @Override
  public TupleExpression ifThenElse(BooleanExpression b, TupleExpression thenExpr, 
      TupleExpression elseExpr) {
    return b.ifThenElse(thenExpr, elseExpr).asTuple();
  }

  @Override
  public TupleExpression incr(TupleExpression expr) {
    return plus(expr, getExpressionManager().bitVectorConstant(offType.getSize(), 1));
  }

  @Override
  public TupleExpression minus(TupleExpression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.isBitVector());
    BitVectorExpression rhsRes = lhs.index(1).asBitVector().minus(rhs);
    return getExpressionManager().tuple(type, lhs.index(0), rhsRes);
  }

  @Override
  public TupleExpression plus(TupleExpression first, Iterable<? extends Expression> rest) {
    Expression lhsRes = first.index(0);
    List<BitVectorExpression> rhsList = Lists.newArrayList(first.index(1).asBitVector());
    for(Expression arg : rest) {
        rhsList.add(arg.asBitVector());
    }
    Expression rhsRes = getExpressionManager().bitVectorPlus(
        offType.getSize(), rhsList);
    return getExpressionManager().tuple(type, lhsRes, rhsRes);
  }
  
  @Override
  public TupleExpression plus(TupleExpression first, Expression... args) {
    return plus(first, Arrays.asList(args));
  }
  
  @Override
  public TupleExpression plus(TupleExpression lhs, Expression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.isBitVector());
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhsRes = lhs_1.plus(offType.getSize(), rhs);
    return getExpressionManager().tuple(type, lhs.index(0), rhsRes);
  } 
  
  @Override
  public BooleanExpression castToBoolean(TupleExpression expr) {
    return neq(expr, nullPtr);
  }
  
  public TupleExpression unknown() {
    return getExpressionManager().variable(UNKNOWN_VARIABLE_NAME, type, true).asTuple();
  }
  
  public TupleExpression nullPtr() {
    return nullPtr;
  }

  @Override
  public TupleExpression ofExpression(Expression x) {
    Preconditions.checkArgument(x.isTuple());
    return x.asTuple();
  }

  @Override
  public Expression index(TupleExpression x, int index) {
    Preconditions.checkArgument(x.size() == 2);
    Preconditions.checkArgument(index < 2 && index >= 0);
    return x.index(index);
  }

  @Override
  public TupleExpression update(TupleExpression x, int index, Expression val) {
    Preconditions.checkArgument(x.size() == 2);
    Preconditions.checkArgument(index < 2 && index >= 0);
    Preconditions.checkArgument(val.getType().equals(
        x.getType().getElementTypes().get(index)));
    return x.update(index, val);
  }
  
  @Override
  public BooleanExpression neq(TupleExpression lhs, TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    return getExpressionManager().or(lhs.index(0)
        .neq(rhs.index(0)), lhs_1.neq(rhs_1));
  }
  
  @Override
  public BooleanExpression eq(TupleExpression lhs, TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == 2 && rhs.size() == 2);
    BitVectorExpression lhs_1 = lhs.index(1).asBitVector();
    BitVectorExpression rhs_1 = rhs.index(1).asBitVector();
    return getExpressionManager().and(lhs.index(0)
        .eq(rhs.index(0)), lhs_1.eq(rhs_1));
  }

  @Override
  public Instance<TupleExpression> getInstance(Iterable<TypeEncoding<?>> elementsEncoding) {
    return new PointerInstance(exprManager, elementsEncoding);
  }

  @Override
  public ExpressionManager getExpressionManager() {
    return exprManager;
  }
  
  @Override
  public boolean isEncodingFor(Expression x) {
    return x.isTuple() && x.asTuple().size() == 2;
  }
}

class PointerInstance implements TupleEncoding.Instance<TupleExpression> {
  private static final String PTR_TYPE_NAME = "ptrType";
  
  private final ExpressionManager exprManager;
  private final Iterable<TypeEncoding<?>> elementsEncoding;
  private final String typeName = PTR_TYPE_NAME;

  public PointerInstance(ExpressionManager exprManager, Iterable<TypeEncoding<?>> elementEncodings) {
    this.exprManager = exprManager;
    this.elementsEncoding = elementEncodings;
  }

  @Override
  public BooleanExpression eq(TupleExpression lhs, TupleExpression rhs) {
    return lhs.eq(rhs);
  }
  
  public boolean equals(Object obj) {
    if( this == obj ) { 
      return true;
    }
    if( !(obj instanceof PointerInstance) ) {
      return false;
    }
    
    PointerInstance instance = (PointerInstance)obj;
    return EqualsUtil.areEqual(exprManager, instance.exprManager)
        && EqualsUtil.areEqual(elementsEncoding, instance.elementsEncoding);
  }

  @Override
  public Iterable<TypeEncoding<?>> getElementsEncoding() {
    return elementsEncoding;
  }

  public ExpressionManager getExpressionManager() {
    return exprManager;
  }
  
  @Override
  public TupleType getType() {
    return exprManager.tupleType(typeName, Iterables.transform(getElementsEncoding(), 
        new Function<TypeEncoding<?>, Type>(){
      @Override
      public Type apply(TypeEncoding<?> encoding) {
        return encoding.getType();
      }
    }));
  }

  @Override
  public int hashCode() {
    int hash = HashCodeUtil.SEED;
    HashCodeUtil.hash(hash, exprManager);
    HashCodeUtil.hash(hash, elementsEncoding);
    return hash;
  }

  @Override
  public boolean isEncodingFor(Expression x) {
    if( !x.isTuple() ) {
      return false;
    }
    TupleExpression ax = x.asTuple();

    if(ax.getType().getElementTypes().size() != Iterables.size(elementsEncoding)) 
      return false;
    
    Iterator<? extends Type> axItr = ax.getType().getElementTypes().iterator();
    Iterator<TypeEncoding<?>> encodingItr = elementsEncoding.iterator();
    while(axItr.hasNext() && encodingItr.hasNext()) {
      if(!axItr.next().equals(encodingItr.next().getType()))
        return false;
    }
    return true;
  }

  @Override
  public TupleExpression ofExpression(Expression x) {
    Preconditions.checkArgument(x.isTuple());
    return x.asTuple();
  }
  
  @Override
  public TupleExpression symbolicConstant(String name, boolean fresh) {
    return variable(name, fresh);
  }

  @Override
  public TupleExpression toTupleExpression(TupleExpression tuple) {
    return tuple;
  }
  
  @Override
  public VariableExpression toVariable(TupleExpression x) {
    Preconditions.checkArgument(x.isVariable());
    return x.asVariable();
  }

  @Override
  public TupleExpression update(TupleExpression tuple,
      int index, Expression val) {  
    return tuple.update(index, val);
  }

  @Override
  public TupleExpression variable(String name, boolean fresh) {
    return exprManager.variable(name, getType(), fresh).asTuple();
  }

  @Override
  public Expression index(TupleExpression tuple, int index) {
    return tuple.index(index);
  }
}

