package edu.nyu.cascade.cvc4;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.UninterpretedVariableExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public final class UninterpretedBoundVariableImpl extends BoundVariableExpressionImpl implements
    UninterpretedVariableExpression {

	protected static UninterpretedBoundVariableImpl create(
      ExpressionManagerImpl exprManager, String name, UninterpretedTypeImpl type, boolean fresh) {
    return new UninterpretedBoundVariableImpl(exprManager,name, type, fresh);
  }

  protected static UninterpretedBoundVariableImpl valueOf(ExpressionManagerImpl em, Expression e) {
	  if (e instanceof UninterpretedBoundVariableImpl && em.equals(e.getExpressionManager())) {
	    return (UninterpretedBoundVariableImpl) e;
	  } else if (e instanceof BoundVariableExpressionImpl) {
	    BoundVariableExpressionImpl e2 = (BoundVariableExpressionImpl)e;
	    return new UninterpretedBoundVariableImpl(em, e2);
	  } else {
	    throw new IllegalArgumentException("Expression type: " + e.getClass());
	  }
	}

	private UninterpretedBoundVariableImpl(ExpressionManagerImpl exprManager, String name, UninterpretedTypeImpl type, boolean fresh) {
    super(exprManager, name, type, fresh);
  }
  
  /** Create a new variable of an integer subtype (e.g., a range type). */
  private UninterpretedBoundVariableImpl(ExpressionManagerImpl em, String name, Type type, boolean fresh) {
    super(em, name, type, fresh);
    Preconditions.checkArgument(type.isUninterpreted());
  }

  /** Copy constructor. */
  private UninterpretedBoundVariableImpl(ExpressionManagerImpl em, VariableExpression x) {
    this(em, x.getName(), x.getType(), false);
  }

  @Override
  public Kind getKind() {
    return Kind.VARIABLE;
  }

  @Override
  public UninterpretedTypeImpl getType() {
    return (UninterpretedTypeImpl) super.getType();
  }
}
