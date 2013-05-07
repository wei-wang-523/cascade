package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.FunctionExpression;
import edu.nyu.cascade.prover.VariableExpression;

public interface Type {

  /**
   * Domain types.
   * 
   * @author dejan
   */
  public enum DomainType {
    BOOLEAN,
    BOUND_VAR_TYPE,
    INTEGER,
    INTEGER_RANGE,
    RATIONAL,
    RATIONAL_RANGE,
    BITVECTOR,
    ARRAY,
    LIST,
    FUNCTION,
    DATATYPE,
    TUPLE,
    RECORD,
    UNINTERPRETED,
    FUNARGS
  }

  /**
   * Returns the type of the domain.
   * 
   * @return the type
   */
  public DomainType getDomainType();

  /*	*//**
   * Is the domain bounded from below.
   * 
   * @return true if bounded
   */
  /*
   * public boolean hasLowerBound();
   *//**
   * Is the domain bounded from above.
   * 
   * @return true if bounded
   */
  /*
   * public boolean hasUpperBound();
   */

  /*	*//**
   * Get the lower bound of this domain
   * 
   * @return the lower bound, null if no bound
   */
  /*
   * public IExpression<T> getLowerBound();
   *//**
   * Get the upper bound of this domain
   * 
   * @return the upper bound, null if no bound
   */
  /*
   * public IExpression<T> getUpperBound();
   */
  /**
   * Get the expression manager responsible for this type.
   * 
   * @return the expression manager
   */
  ExpressionManager getExpressionManager();

  /**
   * Create an IExpression belonging to this type and otherwise equivalent to
   * the given <code>expression</code>. May return the same object if
   * <code>expression</code> belongs to this type.
   * 
   * NOTE (1): Implementations only have to handle kinds of expressions that may
   * possibly have type T. Any other kind of expression should throw an
   * IllegalArgumentException.
   * 
   * NOTE (2): Implementations do not have to handle expressions of kind
   * <code>VARIABLE</code>.
   */
  Expression importExpression(Expression expression);

  /**
   * Returns a function with the given expression as the body, where
   * <code>vars</code> are bound as parameters.
   */
  FunctionExpression lambda(
      Iterable<? extends VariableExpression> vars, Expression body);

  /**
   * Returns a function with the given expression as the body, where
   * <code>var</code> is bound as a parameter.
   */
  FunctionExpression lambda(
      VariableExpression var, Expression body);

  /**
   * Return whether this domain is constant. For example the range [1..10] is a
   * constant domain, and [1..n] is not constant.
   * 
   * @param fresh
   *          TODO
   */
  // boolean isConstant();

  VariableExpression variable(String name, boolean fresh);
  VariableExpression boundVariable(String name, boolean fresh);
  
  boolean isAddableType();
  AddableType asAddableType();

  boolean isComparableType();
  ComparableType asComparableType();

  boolean isMultiplicativeType();
  MultiplicativeType asMultiplicativeType();

  boolean isBitVectorType();
  BitVectorType asBitVectorType();

  boolean isBoolean();
  BooleanType asBooleanType();

  boolean isArrayType();
  ArrayType asArrayType();
  
  boolean isInductive();
  InductiveType asInductive();
  
  boolean isFunction();
  FunctionType asFunction();

  boolean isInteger();
  IntegerType asInteger();

  boolean isRational();
  RationalType asRational();
  
  boolean isTuple();
  TupleType asTuple();
  
  boolean isRecord();
  RecordType asRecord();

  boolean isUninterpreted();
  UninterpretedType asUninterpreted();
}
