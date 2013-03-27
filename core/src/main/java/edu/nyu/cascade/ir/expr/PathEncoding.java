package edu.nyu.cascade.ir.expr;

import java.io.PrintStream;

import edu.nyu.cascade.ir.IRExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.prover.type.Type;

public interface PathEncoding    {
  ExpressionEncoding getExpressionEncoding();
  ExpressionEncoder getExpressionEncoder();
  MemoryModel getMemoryModel();
  Type getPathType();
  
  /**
   * Returns the <code>IExpressionManager</code> object used in the underlying
   * expression encoding.
   */
  ExpressionManager getExpressionManager();

  Expression assume(Expression pre, ExpressionClosure bool);
  Expression assume(Expression pre, IRExpression expr);
  
  /**
   * Add assumptions about memory safe. If option --sound-alloc either 
   * --order-alloc is enabled, memory is assumed to be safe, which means there
   * is no alias or regions overlapping issue. Otherwise, just returns true.
   * @param pre
   * @param bool
   * @return boolean expression
   */
  Expression assumeMemorySafe(Expression pre);

  Expression assign(Expression pre, ExpressionClosure lval, ExpressionClosure rval);
  Expression assign(Expression pre, IRExpression lval, IRExpression rval);
  
  Expression fieldAssign(Expression pre, ExpressionClosure lval, String field, 
      ExpressionClosure rval);
  Expression fieldAssign(Expression pre, IRExpression lval, String field, 
      IRExpression rval);
  
  Expression alloc(Expression pre, ExpressionClosure ptr, ExpressionClosure size);
  Expression alloc(Expression pre, IRExpression ptr, IRExpression size);

  Expression declareArray(Expression pre, ExpressionClosure ptr, ExpressionClosure size);
  Expression declareArray(Expression pre, IRExpression ptr, IRExpression size);

  Expression declareStruct(Expression pre, ExpressionClosure ptr, ExpressionClosure size);
  Expression declareStruct(Expression pre, IRExpression ptr, IRExpression size);
  
  Expression free(Expression pre, ExpressionClosure ptr);
  Expression free(Expression pre, IRExpression ptr);
  
  Expression havoc(Expression pre, IRExpression lval);
  Expression havoc(Expression pre, ExpressionClosure lval);

  Expression emptyPath();
  Expression noop(Expression pre);
  
  ValidityResult<?> checkAssertion(Expression prefix, ExpressionClosure p) throws PathFactoryException;

  SatResult<?> checkPath(Expression prefix) throws PathFactoryException;

  void printCounterExample(PrintStream out, Iterable<?> counterExample) throws PathFactoryException;

}