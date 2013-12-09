package edu.nyu.cascade.fds;

import com.google.inject.Inject;
import com.google.inject.assistedinject.Assisted;
import com.google.common.base.Preconditions;

import edu.nyu.cascade.ir.expr.BooleanEncoding;
import edu.nyu.cascade.ir.expr.IntegerEncoding;
import edu.nyu.cascade.ir.expr.PointerEncoding;
import edu.nyu.cascade.ir.expr.TypeEncoding;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.type.Type;

public class TemporalTypeEncoding<T extends Expression> implements TypeEncoding<StateExpression> {
  private final TypeEncoding<T> baseEncoding;  
  private final StateExpression.Factory stateExprFactory;
  
  @Inject
  protected TemporalTypeEncoding(@Assisted TypeEncoding<T> baseEncoding,
      StateExpression.Factory stateExprFactory) {
    this.baseEncoding = baseEncoding;
    this.stateExprFactory = stateExprFactory;
  }
  
  @Override
  public StateProperty eq(StateExpression a, StateExpression b) {
    return stateExprFactory.valueOf(
        baseEncoding.eq(baseEncoding.ofExpression(a.toExpression()),
            baseEncoding.ofExpression(b.toExpression()))).asStateProperty();
  }

  @Override
  public ExpressionManager getExpressionManager() {
    return baseEncoding.getExpressionManager();
  }

  @Override
  public Type getType() {
    return baseEncoding.getType();
  }

  @Override
  public boolean isEncodingFor(Expression x) {
    return x instanceof StateExpression
        && baseEncoding.isEncodingFor(((StateExpression) x).toExpression());
  }

  @Override
  public StateExpression ofExpression(Expression x) {
    return stateExprFactory.valueOf((Expression)baseEncoding.ofExpression(x));
  }

  @Override
  public StateExpression symbolicConstant(String name, boolean fresh) {
    return stateExprFactory.valueOf((Expression) baseEncoding.symbolicConstant(name, fresh));
  }

  @Override
  public StateVariable toVariable(StateExpression x) {
    Preconditions.checkArgument(x.isVariable());
    return x.asVariable();
  }

  @Override
  public StateExpression variable(String name, boolean fresh) {
    return stateExprFactory.valueOf((Expression) baseEncoding.variable(name,fresh));
  }

	@Override
  public boolean isBooleanEncoding() {
	  return baseEncoding.isBooleanEncoding();
  }

	@Override
  public BooleanEncoding<? extends Expression> asBooleanEncoding() {
	  return baseEncoding.asBooleanEncoding();
  }

	@Override
  public boolean isIntegerEncoding() {
	  return baseEncoding.isIntegerEncoding();
  }

	@Override
  public IntegerEncoding<? extends Expression> asIntegerEncoding() {
	  return baseEncoding.asIntegerEncoding();
  }

	@Override
  public boolean isPointerEncoding() {
	  return baseEncoding.isPointerEncoding();
  }

	@Override
  public PointerEncoding<? extends Expression> asPointerEncoding() {
	  return baseEncoding.asPointerEncoding();
  }
  
}