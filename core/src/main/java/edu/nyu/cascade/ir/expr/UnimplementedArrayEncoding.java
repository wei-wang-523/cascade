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
	  // TODO Auto-generated method stub
	  return null;
    }
  
    @Override
    public BooleanExpression eq(T lhs, T rhs) {
	  // TODO Auto-generated method stub
	  return null;
    }
  
    @Override
    public TypeEncoding<?> getElementEncoding() {
	  // TODO Auto-generated method stub
	  return null;
    }
  
    @Override
    public TypeEncoding<?> getIndexEncoding() {
	  // TODO Auto-generated method stub
	  return null;
    }
  
    @Override
    public Type getType() {
	  // TODO Auto-generated method stub
	  return null;
    }
  
    @Override
    public Expression index(T array, Expression index) {
	  // TODO Auto-generated method stub
	  return null;
    }
  
    @Override
    public boolean isEncodingFor(Expression x) {
	  // TODO Auto-generated method stub
	  return false;
    }
  
    @Override
    public T ofExpression(Expression x) {
	  // TODO Auto-generated method stub
	  return null;
    }
  
    @Override
    public ArrayExpression toArrayExpression(T array) {
	  // TODO Auto-generated method stub
	  return null;
    }
    
    @Override
    public T update(T array, Expression index, Expression val) {
	  // TODO Auto-generated method stub
	  return null;
    }
  
    @Override
    public T variable(String name, boolean fresh) {
	  // TODO Auto-generated method stub
	  return null;
    }

    @Override
    public VariableExpression toVariable(T x) {
	  // TODO Auto-generated method stub
	  return null;
    }

    @Override
    public ExpressionManager getExpressionManager() {
	  // TODO Auto-generated method stub
	  return null;
    }

		@Override
    public boolean isBooleanEncoding() {
	    // TODO Auto-generated method stub
	    return false;
    }

		@Override
    public BooleanEncoding<? extends Expression> asBooleanEncoding() {
			throw new UnsupportedOperationException();
    }

		@Override
    public boolean isIntegerEncoding() {
	    // TODO Auto-generated method stub
	    return false;
    }

		@Override
    public IntegerEncoding<? extends Expression> asIntegerEncoding() {
			throw new UnsupportedOperationException();
    }

		@Override
    public boolean isPointerEncoding() {
	    // TODO Auto-generated method stub
	    return false;
    }

		@Override
    public PointerEncoding<? extends Expression> asPointerEncoding() {
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
    // TODO Auto-generated method stub
	  return false;
  }

  @Override
  public T ofExpression(Expression expr) {
    // TODO Auto-generated method stub
	  return null;
  }

  @Override
  public ExpressionManager getExpressionManager() {
    // TODO Auto-generated method stub
	  return null;
  }

  @Override
  public Expression index(T array, Expression index) {
    // TODO Auto-generated method stub
	  return null;
  }

  @Override
  public T update(T array, Expression index, Expression elem) {
    // TODO Auto-generated method stub
	  return null;
  }

}
