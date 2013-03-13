package edu.nyu.cascade.prover.type;

import com.google.common.collect.ImmutableList;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.InductiveExpression;

public interface InductiveType extends Type {
  InductiveExpression construct(Constructor constructor,
      Expression... args);

  InductiveExpression construct(Constructor constructor,
      Iterable<? extends Expression> args);

  String getName();

  ImmutableList<? extends Constructor> getConstructors();

  Expression select(Selector s, Expression x);

  BooleanExpression test(Constructor c, Expression x);
}
