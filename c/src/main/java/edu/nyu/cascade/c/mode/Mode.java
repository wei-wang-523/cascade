package edu.nyu.cascade.c.mode;

import edu.nyu.cascade.c.preprocessor.PreProcessor;
import edu.nyu.cascade.ir.expr.ExpressionEncoding;
import edu.nyu.cascade.ir.state.StateFactory;
import edu.nyu.cascade.c.CSymbolTable;

public interface Mode {
  ExpressionEncoding getEncoding();
	StateFactory<?> getStateFactory();
	boolean hasPreprocessor();
	PreProcessor<?> buildPreprocessor(CSymbolTable symbolTable);
}
