package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.Expression;

public interface PointerEncoding<T extends Expression> extends TypeEncoding<T> {
  Expression index(T x, int i);
  T update(T x, int index, Expression val);
}
