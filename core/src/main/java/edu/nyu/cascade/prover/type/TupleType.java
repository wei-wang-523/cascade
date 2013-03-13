package edu.nyu.cascade.prover.type;

import java.util.List;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TupleExpression;

public interface TupleType extends Type {
  List<? extends Type> getElementTypes();
  Expression index(Expression tuple, int index);
  int size();
  TupleExpression update(Expression tuple, int index, Expression val);
  String getName();
}
