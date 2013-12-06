package edu.nyu.cascade.ir.expr;

import java.util.Arrays;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.base.Preconditions;
import com.google.common.base.Predicate;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.util.Identifiers;

public class PointerSyncEncoding extends
		AbstractTypeEncoding<TupleExpression> implements 
		PointerEncoding<TupleExpression> {
  private static final String UNKNOWN_VARIABLE_NAME = "bv_encoding_unknown";
  
  private final Type refType;
  private final Type offType;
  private final TupleExpression nullPtr;
  private final int offsetSize;
  
  public static PointerSyncEncoding create(ExpressionManager exprManager, int offsetSize) {
    return new PointerSyncEncoding(exprManager, offsetSize);
  }
  
  private PointerSyncEncoding(ExpressionManager exprManager, int size) {
  	super(exprManager, 
  			exprManager.tupleType(Identifiers.PTR_TYPE_NAME, 
  					exprManager.uninterpretedType(Identifiers.REF_TYPE_NAME), 
  					exprManager.bitVectorType(size)));
  	refType = getType().asTuple().getElementTypes().get(0);
  	offType = getType().asTuple().getElementTypes().get(1);
    nullPtr = exprManager.tuple(getType(), 
    		exprManager.variable(Identifiers.NULL_PTR_NAME, refType, false),
    		exprManager.bitVectorZero(size));
    offsetSize = size;
  }
  
  @Override
  public TupleExpression getNullPtr() {
    return nullPtr;
  }
  
  @Override
  public TupleExpression decr(TupleExpression expr) {
    return minus(expr, constant(1));
  }
  
  @Override
  public BooleanExpression greaterThan(TupleExpression lhs, TupleExpression rhs) {
    Preconditions.checkArgument(isPointer(lhs) && isPointer(rhs));
    BooleanExpression cond1 = lhs.index(0).eq(rhs.index(0));
    BooleanExpression cond2 = getExpressionManager()
    		.greaterThan(lhs.index(1), rhs.index(1));
    return cond1.and(cond2);
  }
  
  @Override
  public BooleanExpression greaterThanOrEqual(TupleExpression lhs, TupleExpression rhs) {
    Preconditions.checkArgument(isPointer(lhs) && isPointer(rhs));
    BooleanExpression cond1 = lhs.index(0).eq(rhs.index(0));
    BooleanExpression cond2 = getExpressionManager()
    		.greaterThanOrEqual(lhs.index(1), rhs.index(1));
    return cond1.and(cond2);
  }
  
  @Override
  public BooleanExpression lessThan(TupleExpression lhs, TupleExpression rhs) {
    Preconditions.checkArgument(isPointer(lhs) && isPointer(rhs));
    BooleanExpression cond1 = lhs.index(0).eq(rhs.index(0));
    BooleanExpression cond2 = getExpressionManager()
    		.lessThan(lhs.index(1), rhs.index(1));
    return cond1.and(cond2);
  }

  @Override
  public BooleanExpression lessThanOrEqual(TupleExpression lhs, TupleExpression rhs) {
    Preconditions.checkArgument(isPointer(lhs) && isPointer(rhs));
    BooleanExpression cond1 = lhs.index(0).eq(rhs.index(0));
    BooleanExpression cond2 = getExpressionManager()
    		.lessThanOrEqual(lhs.index(1), rhs.index(1));
    return cond1.and(cond2);
  }
  
  @Override
  public TupleExpression ifThenElse(BooleanExpression b, TupleExpression thenExpr, 
      TupleExpression elseExpr) {
    return b.ifThenElse(thenExpr, elseExpr).asTuple();
  }

  @Override
  public TupleExpression incr(TupleExpression expr) {
    return plus(expr, constant(1));
  }

  @Override
  public TupleExpression minus(TupleExpression lhs, Expression rhs) {
    Preconditions.checkArgument(isPointer(lhs) && isOffset(rhs));
    Expression rhsRes = offsetMinus(lhs.index(1), rhs);
    return createPointer(lhs.index(0), rhsRes);
  }

  @Override
  public TupleExpression plus(TupleExpression first, Iterable<? extends Expression> rest) {
  	Preconditions.checkArgument(isPointer(first));
  	Preconditions.checkArgument(Iterables.all(rest, new Predicate<Expression>(){
			@Override
			public boolean apply(Expression input) {
				return isOffset(input);
			}
  	}));
  	
    ImmutableList.Builder<Expression> offsetBuilder = 
    		new ImmutableList.Builder<Expression>().add(first.index(1)).addAll(rest);   
    Expression rhsRes = offsetPlus(offsetBuilder.build());
    Expression lhsRes = first.index(0);
    return createPointer(lhsRes, rhsRes);
  }
  
  @Override
  public TupleExpression plus(TupleExpression first, Expression... args) {
    return plus(first, Arrays.asList(args));
  }
  
  @Override
  public TupleExpression plus(TupleExpression lhs, Expression rhs) {
    Preconditions.checkArgument(isPointer(lhs) && isOffset(rhs));
    Expression rhsRes = offsetPlus(lhs.index(1), rhs);
    return createPointer(lhs.index(0), rhsRes);
  } 
  
  @Override
  public BooleanExpression castToBoolean(TupleExpression expr) {
    return neq(expr, nullPtr);
  }
  
  @Override
  public TupleExpression unknown() {
    return variable(UNKNOWN_VARIABLE_NAME, true);
  }

  @Override
  public TupleExpression ofExpression(Expression x) {
    Preconditions.checkArgument(isPointer(x));
    return x.asTuple();
  }

  @Override
  public Expression index(TupleExpression x, int index) {
    Preconditions.checkArgument(isPointer(x));
    Preconditions.checkArgument(index < 2 && index >= 0);
    return x.index(index);
  }

  @Override
  public TupleExpression update(TupleExpression x, int index, Expression val) {
    Preconditions.checkArgument(isPointer(x));
    Preconditions.checkArgument(index < 2 && index >= 0);
    Preconditions.checkArgument(val.getType().equals(
        x.getType().getElementTypes().get(index)));
    return x.update(index, val);
  }
  
  @Override
  public BooleanExpression neq(TupleExpression lhs, TupleExpression rhs) {
    Preconditions.checkArgument(isPointer(lhs) && isPointer(rhs));
    return getExpressionManager().or(lhs.index(0)
        .neq(rhs.index(0)), lhs.index(1).neq(rhs.index(1)));
  }
  
  @Override
  public BooleanExpression eq(TupleExpression lhs, TupleExpression rhs) {
    Preconditions.checkArgument(isPointer(lhs) && isPointer(rhs));
    return getExpressionManager().and(lhs.index(0)
        .eq(rhs.index(0)), lhs.index(1).eq(rhs.index(1)));
  }

	@Override
	public TupleExpression freshPtr(String name, boolean fresh) {
    Expression refVar = getExpressionManager().variable(name, refType, fresh);
    Expression offZero = constant(0);
    return createPointer(refVar, offZero);
	}
	
	private Expression constant(int c) {
		return getExpressionManager().bitVectorConstant(c, offsetSize);
	}
	
	private Expression offsetPlus(Expression lhs, Expression rhs) {
		return getExpressionManager().plus(offsetSize, lhs, rhs);
	}
	
	private Expression offsetPlus(Iterable<Expression> args) {
		return getExpressionManager().plus(offsetSize, args);
	}
	
	private Expression offsetMinus(Expression lhs, Expression rhs) {
		return getExpressionManager().bitVectorMinus(lhs, rhs);
	}
	
	private TupleExpression createPointer(Expression lhs, Expression rhs) {
		return getExpressionManager().tuple(getType(), lhs, rhs);
	}
	
	private boolean isOffset(Expression offset) {
		return offset.getType().equals(offType);
	}
	
	private boolean isPointer(Expression pointer) {
		return pointer.getType().equals(getType());
	}
}