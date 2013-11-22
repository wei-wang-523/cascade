package edu.nyu.cascade.c;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.expr.MemoryModel;
import edu.nyu.cascade.c.CScopeAnalyzer;

public interface Theory {
  ExpressionEncoding getEncoding();
  MemoryModel getMemoryModel();
	PreProcessor.Builder<?> getPreprocessorBuilder();
	CScopeAnalyzer.Builder getScopeAnalyzerBuilder();
}
