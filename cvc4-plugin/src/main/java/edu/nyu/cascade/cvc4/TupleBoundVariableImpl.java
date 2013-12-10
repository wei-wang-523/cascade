package edu.nyu.cascade.cvc4;

import java.util.List;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.TupleVariableExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public final class TupleBoundVariableImpl extends BoundVariableExpressionImpl implements
    TupleVariableExpression {
  
	protected static TupleBoundVariableImpl create(
      ExpressionManagerImpl exprManager, String name, String tname, List<TypeImpl> args, boolean fresh) {
    TupleTypeImpl type = exprManager.tupleType(tname, args);

    return new TupleBoundVariableImpl(exprManager,name, type,fresh);
  }

  protected static TupleBoundVariableImpl create(
      ExpressionManagerImpl exprManager, String name, TupleTypeImpl type, boolean fresh) {
    return new TupleBoundVariableImpl(exprManager,name, type, fresh);
  }

  protected static TupleBoundVariableImpl valueOf(ExpressionManagerImpl em, Expression e) {
	  if (e instanceof TupleBoundVariableImpl && em.equals(e.getExpressionManager())) {
	    return (TupleBoundVariableImpl) e;
	  } else if (e instanceof BoundVariableExpressionImpl) {
	    BoundVariableExpressionImpl e2 = (BoundVariableExpressionImpl)e;
	    return new TupleBoundVariableImpl(em, e2);
	  } else {
	    throw new IllegalArgumentException("Expression type: " + e.getClass());
	  }
	}

	private TupleBoundVariableImpl(ExpressionManagerImpl exprManager, String name, TupleTypeImpl type, boolean fresh) {
    super(exprManager, name, type, fresh);
  }
  
  /** Create a new integer variable. */
  private TupleBoundVariableImpl(ExpressionManagerImpl em, String name, String tname, List<Type> typeArgs, boolean fresh) {
    super(em, name, em.tupleType(tname, typeArgs), fresh);
  }

  /** Create a new variable of an integer subtype (e.g., a range type). */
  private TupleBoundVariableImpl(ExpressionManagerImpl em, String name, Type type, boolean fresh) {
    super(em, name, type, fresh);
    Preconditions.checkArgument(type.isTuple());
  }

  /** Copy constructor. */
  private TupleBoundVariableImpl(ExpressionManagerImpl em, VariableExpression x) {
    this(em, x.getName(), x.getType(), false);
  }

  @Override
  public Kind getKind() {
    return Kind.VARIABLE;
  }

  @Override
  public TupleTypeImpl getType() {
    return (TupleTypeImpl) super.getType();
  }

  @Override
  public Expression index(int i) {
    return TupleExpressionImpl.mkTupleIndex(getExpressionManager(), this, i);
  }

  @Override
  public int size() {
    return getType().size();
  }

  @Override
  public TupleExpression update(int index, Expression val) {
    return TupleExpressionImpl.mkUpdate(getExpressionManager(), this, index, val);
  }
}
