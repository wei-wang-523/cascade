package edu.nyu.cascade.ir.expr;

import java.util.Iterator;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.base.Function;
import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.EqualsUtil;
import edu.nyu.cascade.util.HashCodeUtil;

public class DefaultPointerEncoding implements PointerEncoding<TupleExpression> {
  
  private final ExpressionManager exprManager;
  
  public DefaultPointerEncoding(ExpressionManager exprManager) {
    this.exprManager = exprManager;
  }
  
  @Override
  public TupleExpression ifThenElse(BooleanExpression b, TupleExpression thenExpr, 
      TupleExpression elseExpr) {
    return b.ifThenElse(thenExpr, elseExpr).asTuple();
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
    Preconditions.checkArgument(index < x.size() && index >= 0);
    Preconditions.checkArgument(val.getType().equals(
        x.getType().getElementTypes().get(index)));
    return x.update(index, val);
  }
  
  @Override
  public BooleanExpression neq(TupleExpression lhs, TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == rhs.size());
    return eq(lhs, rhs).not();
  }
  
  @Override
  public BooleanExpression eq(TupleExpression lhs, TupleExpression rhs) {
    Preconditions.checkArgument(lhs.size() == rhs.size());
    ImmutableSet.Builder<BooleanExpression> builder = ImmutableSet.builder();
    for(int i = 0; i < lhs.size(); i++) {
      builder.add(lhs.getChild(i).eq(rhs.getChild(i)));
    }
    return getExpressionManager().and(builder.build());
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
    return x.isTuple();
  }

  @Override
  public TupleExpression decr(TupleExpression expr) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanExpression greaterThan(TupleExpression lhs, TupleExpression rhs) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanExpression greaterThanOrEqual(TupleExpression lhs,
      TupleExpression rhs) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanExpression lessThan(TupleExpression lhs, TupleExpression rhs) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanExpression lessThanOrEqual(TupleExpression lhs,
      TupleExpression rhs) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public TupleExpression incr(TupleExpression expr) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public TupleExpression minus(TupleExpression lhs, Expression rhs) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public TupleExpression plus(TupleExpression first,
      Iterable<? extends Expression> rest) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public TupleExpression plus(TupleExpression first, Expression... rest) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public TupleExpression plus(TupleExpression first, Expression rest) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public BooleanExpression castToBoolean(TupleExpression expr) {
    // TODO Auto-generated method stub
    return null;
  }

	@Override
	public TupleExpression getNullPtr() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public TupleType getType() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public TupleExpression unknown() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public TupleExpression freshPtr(String name, boolean fresh) {
		// TODO Auto-generated method stub
		return null;
	}
}

class DefaultTupleInstance implements PointerEncoding.Instance<TupleExpression> {
  private static final String PTR_TYPE_NAME = "ptrType";
  
  private final ExpressionManager exprManager;
  private final Iterable<TypeEncoding<?>> elementsEncoding;
  private final String typeName = PTR_TYPE_NAME;

  public DefaultTupleInstance(ExpressionManager exprManager, Iterable<TypeEncoding<?>> elementEncodings) {
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
    
    DefaultTupleInstance instance = (DefaultTupleInstance)obj;
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

	@Override
	public TypeEncoding<?> getElementEncoding(int i) {
		return Iterables.get(elementsEncoding, i);
	}
}

