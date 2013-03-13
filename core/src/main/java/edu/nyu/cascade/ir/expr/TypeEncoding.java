package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.prover.type.Type;

public interface TypeEncoding<T extends Expression> {

  /**
   * Comparison for equality between the given expressions.
   * 
   * @param lhs an expression in this encoding
   * @param rhs an expression in this encoding
   * @return a boolean expression
   */
  BooleanExpression eq(T lhs, T rhs);
  
  /**
   * Returns the <code>ExpressionManager</code> object used in the underlying
   * expression encoding.
   */
  ExpressionManager getExpressionManager();

  /** 
   * Get the type used in this encoding.
   */
  Type getType();

  /**
   * Check whether this encoding was used for the given expression. This
   * is a very approximate check: it will typically just check that the
   * types match.
   * 
   * @param x the expression to check
   * @return <code>true</code> if the expression <em>might</em> have been
   * created using this encoding.
   */
  boolean isEncodingFor(Expression x);
  

  /**
   * Convert the given expression to an equivalent expression in the encoding.
   * 
   * @param e an expression of the type handled by this encoding
   * @return an encoded expression
   */  
  T ofExpression(Expression x);
  
  /**
   * A named constant. Creates a constant in the encoding, if it doesn't already
   * exist. If a constant with the same name already exists, it will be returned
   * if <code>fresh</code> is false; a new constant will be created if
   * <code>fresh</code> is true.
   * 
   * @param name
   *          the name of the constant
   * @param fresh
   *          if true, the constant is guaranteed to be unique in the encoding;
   * @return an expression of in the encoding
   */
  Expression symbolicConstant(String name, boolean fresh);
  
  /**
   * Convert an encoded variable to a variable expression
   * 
   * @param x a variable in the encoding
   * @return a variable expression
   */
  VariableExpression toVariable(T x);
  
  /**
   * A variable in the encoding. Creates the variable if it doesn't already
   * exist. If a variable with the same name already exists, it will be returned
   * if <code>fresh</code> is false; a new variable with a mangled name will be
   * created if <code>fresh</code> is true.
   * 
   * @param name
   *          the name of the variable
   * @param fresh
   *          if true, the variable is guaranteed to be unique in the encoding
   * @return an expression encoding the variable 
   */
  T variable(String name, boolean fresh);
}
