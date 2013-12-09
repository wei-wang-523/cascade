package edu.nyu.cascade.prover.type;

import java.util.List;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.TupleExpression;

public interface TupleType extends Type {
  List<? extends Type> getElementTypes();
  int size();
  String getName();
  
  Expression index(Expression tuple, int index);
  TupleExpression update(Expression tuple, int index, Expression value);
}
