package edu.nyu.cascade.prover.type;

import java.util.List;

public interface TupleType extends Type {
  List<? extends Type> getElementTypes();
  int size();
  String getName();
}
