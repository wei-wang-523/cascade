package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TupleExpression;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;

public class UnimplementedPointerEncoding<T extends Expression> implements PointerEncoding<T> {
  private static class Instance<T extends Expression> implements PointerEncoding.Instance<T> {
  
    @Override
    public T symbolicConstant(String name, boolean fresh) {
      throw new UnsupportedOperationException();
    }
  
    @Override
    public BooleanExpression eq(T lhs, T rhs) {
      throw new UnsupportedOperationException();
    }
  
    @Override
    public Type getType() {
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

		@Override
		public TupleExpression toTupleExpression(T tuple) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Expression index(T tuple, int index) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public T update(T tuple, int index, Expression elem) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Iterable<TypeEncoding<?>> getElementsEncoding() {
			// TODO Auto-generated method stub
			return null;
		}
		
		@Override
		public TypeEncoding<?> getElementEncoding(int i) {
			// TODO Auto-generated method stub
			return null;
		}

/*    @Override
    public T valueOf(Object obj) {
      throw new UnsupportedOperationException();
    }*/
  }

  public static <T extends Expression> UnimplementedPointerEncoding<T> create() {
    return new UnimplementedPointerEncoding<T>();
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
	public PointerEncoding.Instance<T> getInstance(
			Iterable<TypeEncoding<?>> elementsEncoding) {
		return new Instance<T>();
	}

	@Override
	public Expression index(T tuple, int index) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public T update(T tuple, int index, Expression elem) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public T decr(T expr) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanExpression greaterThan(T lhs, T rhs) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanExpression greaterThanOrEqual(T lhs, T rhs) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanExpression lessThan(T lhs, T rhs) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanExpression lessThanOrEqual(T lhs, T rhs) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public T ifThenElse(BooleanExpression b, T thenExpr, T elseExpr) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public T incr(T expr) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public T minus(T lhs, Expression rhs) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public T plus(T first, Iterable<? extends Expression> rest) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public T plus(T first, Expression... rest) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public T plus(T first, Expression rest) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanExpression castToBoolean(T expr) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanExpression neq(T lhs, T rhs) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanExpression eq(T lhs, T rhs) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public T getNullPtr() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public TupleType getType() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public T unknown() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public T freshPtr(String name, boolean fresh) {
		// TODO Auto-generated method stub
		return null;
	}

}
