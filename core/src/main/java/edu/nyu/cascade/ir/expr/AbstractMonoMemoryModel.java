package edu.nyu.cascade.ir.expr;

import com.google.common.base.Preconditions;

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

  protected static final String REGION_VARIABLE_NAME = "region";
  protected static final String DEFAULT_MEMORY_VARIABLE_NAME = "m";
  protected static final String DEFAULT_REGION_SIZE_VARIABLE_NAME = "alloc";
  protected static final String DEFAULT_MEMORY_STATE_TYPE = "memType";
  protected static final String DEFAULT_STATE_TYPE = "stateType";
  protected static final String TEST_VAR = "TEST_VAR";
  
  protected enum CellKind {
    SCALAR, POINTER, TEST_VAR
  }
  
  protected xtc.type.Type unwrapped(xtc.type.Type type) {
    while(type.isAlias() || type.isAnnotated() || type.isVariable()) {
      type = type.deannotate();
      type = type.resolve();
    }
    return type;
  }
  
  protected CellKind getCellKind(xtc.type.Type type) {
    Preconditions.checkArgument(type != null);
    type = unwrapped(type);
    if(type.isInteger())
      return CellKind.SCALAR;
    if(type.isPointer())
      return CellKind.POINTER;
    if(type.isLabel() && TEST_VAR.equals(type.toLabel().getName()))
      return CellKind.TEST_VAR;
    throw new IllegalArgumentException("Unknown type " + type);
  }  
  
  protected abstract Expression updateMemoryState(Expression memory, Expression lval, Expression rval);
}
