package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.Expression;

/**
 * Burstall memory model, multiple memory arrays for various type.
 * These arrays types map pointer type to cell type. The state of 
 * memory is a record with multiple arrays for various types.
 * 
 * @author Wei
 *
 */

public abstract class AbstractMonoMemoryModel extends AbstractMemoryModel {
  protected AbstractMonoMemoryModel(ExpressionEncoding encoding) {
    
    super(encoding);
  }
  
  protected abstract Expression updateMemoryState(Expression memory, Expression lval, Expression rval);
}
