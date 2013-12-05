package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.util.Identifiers;

public class DefaultPointerEncoding extends
	AbstractTypeEncoding<TupleExpression> implements 
	PointerEncoding<TupleExpression> {
  
  public DefaultPointerEncoding(ExpressionManager exprManager) {
  	super(exprManager, 
  			exprManager.tupleType(Identifiers.PTR_TYPE_NAME, 
  					exprManager.uninterpretedType(Identifiers.REF_TYPE_NAME), 
  					exprManager.integerType()));
  }
  
  public static DefaultPointerEncoding create(ExpressionManager exprManager) {
    return new DefaultPointerEncoding(exprManager);
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
	public TupleExpression unknown() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public TupleExpression freshPtr(String name, boolean fresh) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
  public BooleanExpression neq(TupleExpression lhs, TupleExpression rhs) {
		return lhs.neq(rhs);
  }

	@Override
  public BooleanExpression eq(TupleExpression lhs, TupleExpression rhs) {
	  return lhs.eq(rhs);
  }
}

