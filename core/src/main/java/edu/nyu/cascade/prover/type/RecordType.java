package edu.nyu.cascade.prover.type;

import java.util.List;

public interface RecordType extends Type {
  List<? extends Type> getElementTypes();
  Type select(String fieldName);
  int size();
  String getName();
  List<String> getElementNames();
}
