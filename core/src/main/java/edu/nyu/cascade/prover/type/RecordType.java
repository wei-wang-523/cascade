package edu.nyu.cascade.prover.type;

import java.util.List;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.RecordExpression;

public interface RecordType extends Type {
  List<? extends Type> getElementTypes();
  Type select(String fieldName);
  int size();
  String getName();
  List<String> getElementNames();
  
	RecordExpression update(Expression record, String fieldName, Expression value);
}
