package edu.nyu.cascade.fds;

import edu.nyu.cascade.fds.StateExpression.Factory;
import edu.nyu.cascade.ir.expr.ArrayEncoding;
import edu.nyu.cascade.ir.expr.TypeEncoding;
import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;

public class TemporalArrayEncoding<T extends Expression> implements
    ArrayEncoding<StateExpression> {

  public static <T extends Expression> TemporalArrayEncoding<T> create(ArrayEncoding<T> baseEncoding,
      Factory exprFactory) {
    return new TemporalArrayEncoding<T>(baseEncoding, exprFactory);
  }
  
  private final ArrayEncoding<T> baseEncoding;
  private final StateExpression.Factory exprFactory;
  
  public TemporalArrayEncoding(ArrayEncoding<T> baseEncoding,
      Factory exprFactory) {
    this.baseEncoding = baseEncoding;
    this.exprFactory = exprFactory;
  }

  @Override
  public ExpressionManager getExpressionManager() {
    return baseEncoding.getExpressionManager();
  }

  class Instance extends TemporalTypeEncoding<T> implements
      ArrayEncoding.Instance<StateExpression> {
    private final ArrayEncoding.Instance<T> baseInstance;
    
    public Instance(ArrayEncoding.Instance<T> baseInstance) {
      super(baseInstance,exprFactory);
      this.baseInstance = baseInstance;
    }
    
    @Override
    public TypeEncoding<?> getElementEncoding() {
      return baseInstance.getElementEncoding();
    }

    @Override
    public TypeEncoding<?> getIndexEncoding() {
      return baseInstance.getIndexEncoding();
    }

    @Override
    public Expression index(StateExpression array, Expression index) {
      return exprFactory.valueOf(baseInstance.index(baseInstance
          .ofExpression(array.toExpression()), index));
    }

    @Override
    public ArrayExpression toArrayExpression(StateExpression array) {
      return baseInstance.toArrayExpression(baseInstance.ofExpression(array.toExpression()));
    }

    @Override
    public StateExpression update(StateExpression array,
        Expression index, Expression elem) {
      return exprFactory.valueOf((Expression)baseInstance.update(baseInstance
          .ofExpression(array.toExpression()), index, elem));
    }

  }

  @Override
  public edu.nyu.cascade.ir.expr.ArrayEncoding.Instance<StateExpression> getInstance(
      TypeEncoding<?> indexEncoding, TypeEncoding<?> elementEncoding) {
    return new Instance(baseEncoding.getInstance(indexEncoding, elementEncoding));
  }

  @Override
  public boolean isEncodingFor(Expression x) {
    return x instanceof StateExpression
        && baseEncoding.isEncodingFor(((StateExpression) x).toExpression());
  }

  @Override
  public StateExpression ofExpression(Expression expr) {
    return exprFactory.valueOf((Expression)baseEncoding.ofExpression(expr));
  }

  @Override
  public StateExpression index(StateExpression array, Expression index) {
    return exprFactory.valueOf(baseEncoding.index(baseEncoding.ofExpression(array), index));
  }

  @Override
  public StateExpression update(StateExpression array, Expression index,
      Expression elem) {
    return exprFactory.valueOf(baseEncoding.update(baseEncoding.ofExpression(array), index, elem));
  }

}
