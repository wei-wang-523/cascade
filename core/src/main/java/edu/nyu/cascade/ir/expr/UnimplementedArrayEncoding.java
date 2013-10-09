package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public class UnimplementedArrayEncoding<T extends Expression> implements ArrayEncoding<T> {
  private static class Instance<T extends Expression> implements ArrayEncoding.Instance<T> {
  
    @Override
    public T symbolicConstant(String name, boolean fresh) {
      throw new UnsupportedOperationException();
    }
  
    @Override
    public BooleanExpression eq(T lhs, T rhs) {
      throw new UnsupportedOperationException();
    }
  
    @Override
    public TypeEncoding<?> getElementEncoding() {
      throw new UnsupportedOperationException();
    }
  
    @Override
    public TypeEncoding<?> getIndexEncoding() {
      throw new UnsupportedOperationException();
    }
  
    @Override
    public Type getType() {
      throw new UnsupportedOperationException();
    }
  
    @Override
    public Expression index(T array, Expression index) {
      throw new UnsupportedOperationException();
    }
  
    @Override
    public boolean isEncodingFor(Expression x) {
      throw new UnsupportedOperationException();
    }
  
    @Override
    public T ofExpression(Expression x) {
      throw new UnsupportedOperationException();
    }
  
    @Override
    public ArrayExpression toArrayExpression(T array) {
      throw new UnsupportedOperationException();
    }
    
    @Override
    public T update(T array, Expression index, Expression val) {
      throw new UnsupportedOperationException();
    }
  
    @Override
    public T variable(String name, boolean fresh) {
      throw new UnsupportedOperationException();
    }

    @Override
    public VariableExpression toVariable(T x) {
      throw new UnsupportedOperationException();
    }

    @Override
    public ExpressionManager getExpressionManager() {
      throw new UnsupportedOperationException();
    }
  }

  public static <T extends Expression> UnimplementedArrayEncoding<T> create() {
    return new UnimplementedArrayEncoding<T>();
  }
  
  @Override
  public ArrayEncoding.Instance<T> getInstance(
      TypeEncoding<?> indexEncoding, TypeEncoding<?> elementEncoding) {
    return new Instance<T>();
  }

  @Override
  public boolean isEncodingFor(Expression x) {
    throw new UnsupportedOperationException();
  }

  @Override
  public T ofExpression(Expression expr) {
    throw new UnsupportedOperationException();
  }

  @Override
  public ExpressionManager getExpressionManager() {
    throw new UnsupportedOperationException();
  }

  @Override
  public Expression index(T array, Expression index) {
    throw new UnsupportedOperationException();
  }

  @Override
  public T update(T array, Expression index, Expression elem) {
    throw new UnsupportedOperationException();
  }

}
