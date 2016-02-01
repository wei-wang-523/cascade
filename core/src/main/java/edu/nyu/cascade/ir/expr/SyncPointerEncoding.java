package edu.nyu.cascade.ir.expr;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;

import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.util.Identifiers;

public class SyncPointerEncoding <T extends Expression, S extends Expression>
  extends AbstractTypeEncoding<TupleExpression>
	implements PointerEncoding<TupleExpression> {

	private static final String UNKNOWN_VARIABLE_NAME = "ptr_encoding_unknown";
	
	private final UninterpretedEncoding<S> baseEncoding;
	private final IntegerEncoding<T> offsetEncoding;
	
  @SuppressWarnings("unchecked")
  private SyncPointerEncoding(TupleEncoding.Instance<TupleExpression> tupleEncodingInstance) {
  	super(tupleEncodingInstance.getExpressionManager(), tupleEncodingInstance.getType());
		Preconditions.checkArgument(Iterables.size(tupleEncodingInstance.getElementEncodings()) == 2);
		
		Iterable<TypeEncoding<?>> elementEncodings = tupleEncodingInstance.getElementEncodings();
		TypeEncoding<?> elementEncoding_0 = Iterables.get(elementEncodings, 0);
		TypeEncoding<?> elementEncoding_1 = Iterables.get(elementEncodings, 1);
		
		Preconditions.checkArgument(elementEncoding_0 instanceof UninterpretedEncoding);
		Preconditions.checkArgument(elementEncoding_1 instanceof IntegerEncoding);
		
		baseEncoding = (UninterpretedEncoding<S>) elementEncoding_0;
		offsetEncoding = (IntegerEncoding<T>) elementEncoding_1;
	}
  
  @SuppressWarnings({ "unchecked", "rawtypes" })
  public static SyncPointerEncoding<?, ?> create(TupleEncoding.Instance<TupleExpression> instance) {
  	return new SyncPointerEncoding(instance);
  }
  
  public UninterpretedEncoding<? extends Expression> getBaseEncoding() {
  	return baseEncoding;
  }
  
  public IntegerEncoding<T> getOffsetEncoding() {
  	return offsetEncoding;
  }
  
	private boolean isOffset(Expression expr) {
	  return getOffsetEncoding().isEncodingFor(expr);
	}
	
	private boolean isPointer(Expression expr) {
		return expr.getType().equals(getType());
	}
	
	private T minus_(IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isOffset(lhs));
    Preconditions.checkArgument(isOffset(rhs));
    return ie.minus(ie.ofExpression(lhs), ie.ofExpression(rhs));
	}

	private T plus_(IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isOffset(lhs));
    Preconditions.checkArgument(isOffset(rhs));
    return ie.plus(ie.ofExpression(lhs), ie.ofExpression(rhs));
	}
	
	private T plus_(final IntegerEncoding<T> ie, Expression first, Iterable<? extends Expression> rest) {
	  Iterable<T> iTerms = Iterables.transform(rest, new Function<Expression, T>(){
			@Override
			public T apply(Expression input) {
				Preconditions.checkArgument(isOffset(input));
				return ie.ofExpression(input);
			}
	  });
	  return ie.plus(ie.ofExpression(first), iTerms);
	}
	
	private BooleanExpression lessThan_(IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
	  Preconditions.checkArgument(isOffset(lhs));
	  Preconditions.checkArgument(isOffset(rhs));
	  return ie.lessThan(ie.ofExpression(lhs), ie.ofExpression(rhs));
	}
	
	private BooleanExpression lessThanOrEqual_(IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
		Preconditions.checkArgument(isOffset(lhs));
	  Preconditions.checkArgument(isOffset(rhs));
	  return ie.lessThanOrEqual(ie.ofExpression(lhs), ie.ofExpression(rhs));
	}
	
	private BooleanExpression greaterThan_(IntegerEncoding<T> ie,
	    Expression lhs, Expression rhs) {
	  Preconditions.checkArgument(isOffset(lhs));
	  Preconditions.checkArgument(isOffset(rhs));
	  return ie.greaterThan(ie.ofExpression(lhs), ie.ofExpression(rhs));
	}
	
  private BooleanExpression greaterThanOrEqual_(
  		IntegerEncoding<T> ie, Expression lhs, Expression rhs) {
    Preconditions.checkArgument(isOffset(lhs));
    Preconditions.checkArgument(isOffset(rhs));
    return ie.greaterThanOrEqual(ie.ofExpression(lhs), ie.ofExpression(rhs));
  }

	@Override
  public TupleExpression variable(String name, IRType type, boolean fresh) {
	  return getExpressionManager().variable(name, getType(), fresh).asTuple();
  }

	@Override
  public TupleExpression ofExpression(Expression expr) {
	  Preconditions.checkArgument(isPointer(expr));
	  return expr.asTuple();
  }

	@Override
  public TupleExpression ifThenElse(BooleanExpression b,
      TupleExpression thenExpr, TupleExpression elseExpr) {
	  return b.ifThenElse(thenExpr, elseExpr).asTuple();
  }

	@Override
  public TupleExpression incr(TupleExpression expr) {
	  Preconditions.checkArgument(isPointer(expr));
	  return plus(expr, getOffsetEncoding().one());
  }

	@Override
  public TupleExpression decr(TupleExpression expr) {
	  Preconditions.checkArgument(isPointer(expr));
	  return minus(expr, getOffsetEncoding().one());
  }

	@Override
  public TupleExpression minus(TupleExpression lhs, Expression rhs) {
	  Preconditions.checkArgument(isPointer(lhs));
	  Preconditions.checkArgument(isOffset(rhs));
	  Expression base = lhs.asTuple().index(0);
	  Expression offset = lhs.asTuple().index(1);
	  Expression resOffset = minus_(getOffsetEncoding(), offset, rhs);
	  return getExpressionManager().tuple(getType(), base, resOffset);
  }
	
  @Override
	public TupleExpression plus(TupleExpression lhs, Expression rhs) {
	  Preconditions.checkArgument(isPointer(lhs));
	  Preconditions.checkArgument(isOffset(rhs));
	  Expression base = lhs.asTuple().index(0);
	  Expression offset = lhs.asTuple().index(1);
	  Expression resOffset = plus_(getOffsetEncoding(), offset, rhs);
	  return getExpressionManager().tuple(getType(), base, resOffset);
	}

	@Override
	public TupleExpression plus(TupleExpression first, Expression... rest) {
		return plus(first, Lists.newArrayList(rest));
	}

	@Override
  public TupleExpression plus(TupleExpression first,
      Iterable<? extends Expression> rest) {
	  Preconditions.checkArgument(isPointer(first));
	  Expression base = first.asTuple().index(0);
	  Expression offset = first.asTuple().index(1);
	  Expression resOffset = plus_(getOffsetEncoding(), offset, rest);
	  return getExpressionManager().tuple(getType(), base, resOffset);
  }

	@Override
  public BooleanExpression toBoolean(TupleExpression expr) {
	  return expr.neq(getNullPtr());
  }

	@Override
  public BooleanExpression neq(TupleExpression lhs, TupleExpression rhs) {
	  return lhs.neq(rhs);
  }

	@Override
  public BooleanExpression greaterThan(TupleExpression lhs, TupleExpression rhs) {
		Preconditions.checkArgument(isPointer(lhs));
		Preconditions.checkArgument(isPointer(rhs));
		Expression lbase = lhs.asTuple().index(0);
	  Expression loffset = lhs.asTuple().index(1);
	  Expression rbase = rhs.asTuple().index(0);
	  Expression roffset = rhs.asTuple().index(1);
	  return getExpressionManager().and(lbase.eq(rbase),
	  		greaterThan_(getOffsetEncoding(), loffset, roffset));
  }

	@Override
  public BooleanExpression greaterThanOrEqual(TupleExpression lhs,
      TupleExpression rhs) {
		Preconditions.checkArgument(isPointer(lhs));
		Preconditions.checkArgument(isPointer(rhs));
		Expression lbase = lhs.asTuple().index(0);
	  Expression loffset = lhs.asTuple().index(1);
	  Expression rbase = rhs.asTuple().index(0);
	  Expression roffset = rhs.asTuple().index(1);
	  return getExpressionManager().and(lbase.eq(rbase),
	  		greaterThanOrEqual_(getOffsetEncoding(), loffset, roffset));
  }

	@Override
  public BooleanExpression lessThan(TupleExpression lhs, TupleExpression rhs) {
		Preconditions.checkArgument(isPointer(lhs));
		Preconditions.checkArgument(isPointer(rhs));
		Expression lbase = lhs.asTuple().index(0);
	  Expression loffset = lhs.asTuple().index(1);
	  Expression rbase = rhs.asTuple().index(0);
	  Expression roffset = rhs.asTuple().index(1);
	  return getExpressionManager().and(lbase.eq(rbase),
	  		lessThan_(getOffsetEncoding(), loffset, roffset));
  }

	@Override
  public BooleanExpression lessThanOrEqual(TupleExpression lhs,
      TupleExpression rhs) {
		Preconditions.checkArgument(isPointer(lhs));
		Preconditions.checkArgument(isPointer(rhs));
		Expression lbase = lhs.asTuple().index(0);
	  Expression loffset = lhs.asTuple().index(1);
	  Expression rbase = rhs.asTuple().index(0);
	  Expression roffset = rhs.asTuple().index(1);
	  return getExpressionManager().and(lbase.eq(rbase),
	  		lessThanOrEqual_(getOffsetEncoding(), loffset, roffset));
  }

	@Override
  public TupleExpression getNullPtr() {
	  Expression base = getBaseEncoding().variable(Identifiers.NULL_PTR_NAME, false);
	  Expression offset = getOffsetEncoding().zero();
	  return getExpressionManager().tuple(getType(), base, offset);
  }

	@Override
  public TupleExpression unknown() {
		return variable(UNKNOWN_VARIABLE_NAME, true);
  }

	@Override
  public TupleExpression freshPtr(String name, boolean fresh) {
    Expression refVar = getBaseEncoding().variable(name, fresh);
    Expression offZero = getOffsetEncoding().zero();
    return getExpressionManager().tuple(getType(), refVar, offZero);
  }

	@Override
  public boolean isSyncEncoding() {
	  return true;
  }

	@Override
  public boolean isLinearEncoding() {
	  return false;
  }

	@Override
  public LinearPointerEncoding<? extends Expression> asLinearPointerEncoding() {
	  throw new UnsupportedOperationException();
  }
	
	@Override
	public SyncPointerEncoding<T, S> asSyncPointerEncoding() {
		return this;
	}
}
