package edu.nyu.cascade.c;

import edu.nyu.cascade.c.preprocessor.PreProcessor.Builder;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;

public interface Theory {
  ExpressionEncoding getEncoding();
  MemoryModel getMemoryModel();
	Builder<?> getPreprocessorBuilder();
}
