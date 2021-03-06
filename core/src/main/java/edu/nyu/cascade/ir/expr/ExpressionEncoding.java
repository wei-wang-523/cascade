package edu.nyu.cascade.ir.expr;

import java.math.BigInteger;

import xtc.type.Type;

import com.google.common.collect.ImmutableSet;

import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.ir.type.IRType;
import edu.nyu.cascade.prover.BooleanExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.VariableExpression;
import edu.nyu.cascade.util.Pair;

/**
 * An encoding of program expressions.
 * 
 * Operations on arrays are optional: arrays are treated here as
 * first-class values, which may not be appropriate in some encodings.
 * (E.g., in a bit-precise encoding for C programs, the representation of 
 * arrays will be embedded in the memory model, not the expression encoding.)
 * 
 * @author <a href="mailto:cconway@cs.nyu.edu">Christopher Conway</a>
 */

public interface ExpressionEncoding {
  
  /**
   * Add <code>assumption</code> to be asserted as axioms in backend solver
   * @param assumption
   * @return
   */
  boolean addAssumption(BooleanExpression assumption);

  /**
   * The logical AND of the given expressions. 
   * 
   * @param lhs a boolean-encoded expression
   * @param rhs a boolean-encoded expression
   * @return a boolean-encoded expression
   */
  Expression and(Expression lhs, Expression rhs) ;

  /**
   * The logical AND of the given expressions. 
   * 
   * @param conjuncts boolean-encoded expressions
   * @return a boolean-encoded expression
   */
  Expression and(Expression... conjuncts);
  
  /**
   * The logical AND of the given expressions.
   * 
   * @param conjuncts boolean-encoded expressions
   * @return a boolean-encoded expression
   */
  Expression and(Iterable<? extends Expression> conjuncts) ;

  /**
   * The bitwise AND of the given expressions.
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression bitwiseAnd(Expression lhs, Expression rhs) ;
  
  /**
   * The bitwise OR of the given expressions.
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression bitwiseOr(Expression lhs, Expression rhs) ;
  
  /**
   * The bitwise XOR of the given expressions.
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression bitwiseXor(Expression lhs, Expression rhs) ;

  /**
   * The bitwise NEGATE of the given expression.
   * 
   * @param src an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression bitwiseNegate(Expression src);

	/**
   * The conversion of the given expression to a boolean, according to the
   * conversion rule of the underlying encoding.
   * 
   * @param e a boolean- or integer-encoded expression
   * @return an boolean-encoded expression
   */
  Expression castToBoolean(Expression e) ;

  /**
   * The conversion of the given expression to an integer, according to the
   * conversion rule of the underlying encoding.
   * 
   * @param e a boolean- or integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression castToInteger(Expression e) ;
  
  /**
   * The conversion of the given expression to an integer, according to the
   * conversion rule of the underlying encoding.
   * 
   * @param e an integer-encoded expression
   * @return an integer-encoded expression with given size
   */
  Expression castToInteger(Expression e, int size) ;
  
  /**
   * The conversion of the given expression to an integer, according to the
   * conversion rule of the underlying encoding.
   * 
   * @param e an integer-encoded expression
   * @return an integer-encoded expression with given size
   */
  Expression castToInteger(Expression e, int size, boolean signed) ;
  
  /**
   * The conversion of the given expression to a pointer, according to the
   * conversion rule of the underlying encoding.
   * 
   * @param e a boolean- or pointer- integer-encoded expression
   * @return an pointer-encoded expression
   */
  Expression castToPointer(Expression e) ;
  
/*  *//**
   * The conversion of the given expression to a rational, according to the
   * conversion rule of the underlying encoding.
   * 
   * @param e a boolean- or integer-encoded expression
   * @return a rational-encoded expression
   *//*
  Expression castToRational(Expression e) ;*/

  /**
   * A shortcut for <code>minus(e,one())</code>.
   *
   * @param e an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression decr(Expression e) ;
  
  /**
   * A comparison for disequality between all of the input expressions.
   * 
   * @param exprs
   *          expressions of the same encoded type
   * @return a boolean-encoded expression
   */
  Expression distinct(Iterable<? extends Expression> exprs);

  /**
   * Comparison for equality between the given expressions.
   *
   * @param lhs an expression
   * @param rhs an expression (of the same encoded type as <code>lhs</code>)
   * @return a boolean-encoded expression
   */
  Expression eq(Expression lhs, Expression rhs) ;

  /**
   * The universal quantification ("exists") of <code>p</code> by the variable
   * <code>var</code>.
   * 
   * @param var
   *          a variable in the encoding
   * @param p
   *          a boolean-encoded expression
   * @return a boolean-encoded expression
   */
  Expression exists(Expression var, Expression p) ;
  
  Expression exists(Expression var1, Expression var2, Expression body);
  
  Expression exists(Expression var1, Expression var2, Expression var3,
      Expression body);
  
  Expression exists(Iterable<? extends Expression> vars,
      Expression body);
  
  /**
   * The boolean expression <code>false</code>.
   */
  Expression ff() ;

  /**
   * The universal quantification ("for all") of <code>p</code> by the variable
   * <code>var</code>.
   * 
   * @param var
   *          a variable in the encoding
   * @param p
   *          a boolean-encoded expression
   * @return a boolean-encoded expression
   */
  Expression forall(Expression var, Expression p) ;
  
  Expression forall(Expression var1, Expression var2, Expression body);
  
  Expression forall(Expression var1, Expression var2, Expression var3,
      Expression body);
  
  Expression forall(Iterable<? extends Expression> vars,
      Expression body);

  /**
   * An interpreted function application.
   * 
   * @param name the name of the function
   * @param args expressions in the encoding
   * @return an expression encoded as appropriate for the function
   */
  Expression functionCall(String name, Iterable<? extends Expression> args) ;

  /**
   * An interpreted function application.
   * 
   * @param name the name of the function
   * @param args expressions in the encoding
   * @return an expression encoded as appropriate for the function
   */
  Expression functionCall(String name, Expression... args) ;

  /**
   * The underlying array encoding.
   */
  ArrayEncoding<?> getArrayEncoding();
  
  /**
   * The underlying tuple encoding.
   */
  PointerEncoding<? extends Expression> getPointerEncoding();

  /**
   * Get logical assumptions used in the underlying encoding. E.g., if variables
   * <code>x</code>, <code>y</code>, and <code>z</code> are represented as
   * indices into an array, then <code>getAssumptions()</code> may return
   * <code>{ x ≠ y, x ≠ z, y ≠ z }</code>.
   */
  ImmutableSet<? extends BooleanExpression> getAssumptions();
  
  /**
   * Clear the assumptions
   */
	void clearAssumptions();

  /**
   * The underlying boolean encoding.
   */
  BooleanEncoding<?> getBooleanEncoding();

  /**
   * Returns the <code>IExpressionManager</code> object used in the underlying
   * expression encoding.
   */
  ExpressionManager getExpressionManager();
  
  /**
   * Get C type analyzer
   */
  CType getCTypeAnalyzer();

  /**
   * The underlying integer encoding.
   */
  IntegerEncoding<?> getIntegerEncoding();
  
  /**
   * A greater-than comparison between the given expressions
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @param a boolean-encoded expression
   */
  Expression greaterThan(Expression lhs, Expression rhs) ;
  
  /**
   * A greater-than comparison between the given pointer expressions
   * 
   * @param lhs an pointer-encoded expression
   * @param rhs an pointer-encoded expression
   * @param a boolean-encoded expression
   */
  Expression pointerGreaterThan(Expression lhs, Expression rhs) ;
  
  /**
   * A greater-than comparison between the given expressions
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @param a boolean-encoded expression
   */
  Expression signedGreaterThan(Expression lhs, Expression rhs) ;
  
  /**
   * A "greater-than or equal" comparison between the given expressions
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @param a boolean-encoded expression
   */
  Expression greaterThanOrEqual(Expression lhs, Expression rhs);
  
  /**
   * A "greater-than or equal" comparison between the given pointer expressions
   * 
   * @param lhs an pointer-encoded expression
   * @param rhs an pointer-encoded expression
   * @param a boolean-encoded expression
   */
  Expression pointerGreaterThanOrEqual(Expression lhs, Expression rhs);
  
  /**
   * A "signed greater-than or equal" comparison between the given expressions
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @param a boolean-encoded expression
   */
  Expression signedGreaterThanOrEqual(Expression lhs, Expression rhs);
  
  /**
   * An ITE expression.
   * 
   * @param bool
   *          a boolean-encoded expression
   * @param thenExpr
   *          the value of the expression if <code>bool</code> is
   *          <code>true</code>
   * @param elseExpr
   *          the value of the expression if <code>bool</code> is
   *          <code>false</code> (of the same encoded type as
   *          <code>thenExpr</code>)
   * @return an expression of the same encoded type as <code>thenExpr</code> and
   *         <code>elseExpr</code>
   */
  Expression ifThenElse(Expression bool, Expression thenExpr, Expression elseExpr);

  
  /**
   * An boolean expression
   * 
   * @param assumption
   * 					a boolean-encoded expression
   * @param assertion
   * 					a boolean-encoded expression
   * @return an expression of <code>assumption.implies(assertion)</code>
   */
  Expression implies(Expression assumption, Expression assertion);
  
  /**
   * A shortcut for <code>plus(e,one())</code>.
   * 
   * @param e an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression incr(Expression e) ;

  /**
   * An array read.
   * 
   * @param array an array in the encoding
   * @param index an expression (of the same encoded type as <code>array</code>'s indices)
   * @return an expression of the same encoded type as <code>array</code>'s elements
   */
  Expression indexArray(Expression array, Expression index);

  /**
   * A shortcut for <code>and(castToBoolean(lhs),castToBoolean(rhs))</code>.
   * 
   * @param lhs a boolean- or integer-encoded expression
   * @param rhs a boolean- or integer-encoded expression
   * @return a boolean-encoded expression
   */
  Expression integerAnd(Expression lhs, Expression rhs) ;
  
  /** 
   * An encoded integer constant.
   * 
   * @param c the integer
   * @return an integer-encoded expression
   */
  Expression integerConstant(int c) ;
  
  /** 
   * An encoded integer constant.
   * 
   * @param c the long number
   * @return an integer-encoded expression
   */
  Expression integerConstant(long c) ;
  
  /** 
   * An encoded character constant.
   * 
   * @param c the int number
   * @return an integer-encoded expression
   */
  Expression characterConstant(int c) ;
  
  /** 
   * An encoded integer constant.
   * 
   * @param c the BigInteger number
   * @return an integer-encoded expression
   */
  Expression integerConstant(BigInteger c, long size) ;
  
  /**
   * A shortcut for <code>not(castToBoolean(e))</code>.
   * 
   * @param e a boolean- or integer-encoded expression
   * @return a boolean-encoded expression
   */
  Expression integerNot(Expression e) ;

  /**
   * A shortcut for <code>or(castToBoolean(lhs),castToBoolean(rhs))</code>.
   * 
   * @param lhs a boolean- or integer-encoded expression
   * @param rhs a boolean- or integer-encoded expression
   * @return a boolean-encoded expression
   */
  Expression integerOr(Expression lhs, Expression rhs) ;

  /**
   * Tests whether the given expression is an array in the encoding.
   */
  boolean isArray(Expression e);

  /**
   * Tests whether the given expression is an boolean in the encoding.
   */
  boolean isBoolean(Expression e);
  
  /**
   * Tests whether the given expression is an integer in the encoding.
   */
  boolean isInteger(Expression e);
  
  boolean isPointer(Expression expr);

	/**
   * Tests whether the given expression is a variable in the encoding.
   */
  boolean isVariable(Expression e);

  /**
   * A less-than comparison between the given expressions
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @param a boolean-encoded expression
   */
  Expression lessThan(Expression lhs, Expression rhs) ;
  
  /**
   * A less-than comparison between the given pointer expressions
   * 
   * @param lhs an pointer-encoded expression
   * @param rhs an pointer-encoded expression
   * @param a boolean-encoded expression
   */
  Expression pointerLessThan(Expression lhs, Expression rhs) ;
  
  /**
   * A signed less-than comparison between the given expressions
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @param a boolean-encoded expression
   */
  Expression signedLessThan(Expression lhs, Expression rhs) ;

  /**
   * A "less-than or equal" comparison between the given expressions
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @param a boolean-encoded expression
   */
  Expression lessThanOrEqual(Expression lhs, Expression rhs) ;
  
  /**
   * A "less-than or equal" comparison between the given pointer expressions
   * 
   * @param lhs an pointer-encoded expression
   * @param rhs an pointer-encoded expression
   * @param a boolean-encoded expression
   */
  Expression pointerLessThanOrEqual(Expression lhs, Expression rhs) ;
  
  /**
   * A "signed less-than or equal" comparison between the given expressions
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @param a boolean-encoded expression
   */
  Expression signedLessThanOrEqual(Expression lhs, Expression rhs) ;
  
  /**
   * Subtracting to integers.
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression minus(Expression lhs, Expression rhs) ;
  
  /**
   * The multiplication of the given expressions. 
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression times(Expression lhs, Expression rhs) ;

  /**
   * The division of the given expressions. 
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression divide(Expression lhs, Expression rhs) ;
  
  /**
   * The division of the given expressions. 
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @return a signed integer-encoded expression
   */
  Expression signedDivide(Expression lhs, Expression rhs) ;
  
  /**
   * The remainder of the given expressions. 
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression rem(Expression lhs, Expression rhs) ;
  

  /**
   * The modulo of the given expressions. 
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression mod(Expression lhs, Expression rhs);
  
  /**
   * The signed remainder of the given expressions. 
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @return a signed integer-encoded expression
   */
  Expression signedRem(Expression lhs, Expression rhs) ;
  
  /**
   * Negate an integer.
   * 
   * @param e an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression negate(Expression e) ;

  /**
   * A comparision for disequality.
   * 
   * @param lhs an expression
   * @param rhs an expression of the same encoded types as <code>lhs</code>
   * @return a boolean-encoded expression
   */
  Expression neq(Expression lhs, Expression rhs) ;
  
  /**
   * A logical NOR ("not-or") expression.
   * 
   * @param disjuncts boolean-encoded expressions
   * @return a boolean-encoded expression
   */
  Expression nor(Iterable<Expression> disjuncts) ;

  /**
   * A logical NOT expression.
   * 
   * @param b a boolean-encoded expression
   * @return a boolean encoded expression
   */
  Expression not(Expression b) ;

  /**
   * Convert a boolean expression to a boolean in the encoding.
   * 
   * @param e
   *          an expression of boolean type (i.e., e.isBoolean() should return
   *          true)
   * @return a boolean-encoded expression
   */
  Expression ofBoolean(Expression e);
  
  /** 
   * Convert an integer expression to an integer in the encoding.
   * 
   * @param e
   *          an expression of integer type (i.e., e.isInteger() should return
   *          true)
   * @return an integer-encoded expression
   * */
  Expression ofInteger(Expression e);

  /** 
   * Convert a tuple expression to a pointer in the encoding.
   * 
   * @param e
   *          an expression of tuple type (i.e., e.isTuple() should return
   *          true)
   * @return an pointer-encoded expression
   * */
  Expression ofPointer(Expression e);
  
  /**
   * The integer constant 1. May be more efficient than
   * <code>integerConstant(1)</code> in some implementations.
   */
  Expression one() ;

  /**
   * The logical OR of the given expressions. 
   * 
   * @param lhs a boolean-encoded expression
   * @param rhs a boolean-encoded expression
   * @return a boolean-encoded expression
   */
  Expression or(Expression lhs, Expression rhs) ;
  
  /**
   * The logical OR of the given expressions. 
   * 
   * @param disjuncts boolean-encoded expressions
   * @return a boolean-encoded expression
   */
  Expression or(Expression... disjuncts) ;

  /**
   * The logical OR of the given expressions. 
   * 
   * @param disjuncts boolean-encoded expressions
   * @return a boolean-encoded expression
   */
  Expression or(Iterable<? extends Expression> conjuncts) ;

  /**
   * The addition of the given expressions. 
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression plus(Expression lhs, Expression rhs) ;
  
  /**
   * The addition of the given expressions. 
   * 
   * @param first an integer-encoded expression
   * @param rest integer-encoded expressions
   * @return an integer-encoded expression
   */
  Expression plus(Expression first, Expression... rest) ;

  /**
   * The addition of the given expressions. 
   * 
   * @param first an integer-encoded expression
   * @param rest integer-encoded expressions
   * @return an integer-encoded expression
   */
  Expression plus(Expression first, Iterable<? extends Expression> args) ;
  
  /**
   * The left shift of the given expressions. 
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression lshift(Expression lhs, Expression rhs) ;
  
  /**
   * The right shift of the given expressions. 
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression rshift(Expression lhs, Expression rhs) ;
  
  /**
   * The signed right shift of the given expressions. 
   * 
   * @param lhs an integer-encoded expression
   * @param rhs an integer-encoded expression
   * @return an integer-encoded expression
   */
  Expression signedRshift(Expression lhs, Expression rhs) ;

  /**
   * Convert a boolean expression to a <code>BooleanExpression</code>.
   *    
   * @param e a boolean-encoded expression
   * @return a <code>BooleanExpression</code> with the same value
   */
  BooleanExpression toBoolean(Expression e);
  
  /**
   * The boolean expression <code>true</code>.
   */
  Expression tt() ;
  
  /**
   * An expression with unary minus
   */
  Expression uminus(Expression expr);

  /**
   * An expression with unary minus
   */
  Expression uplus(Expression expr);
  
  /**
   * An array write.
   * 
   * @param array an array in the encoding
   * @param index an expression of the same encoded type as <code>array</code>'s indices
   * @param newValue an expression of the same encoded type as <code>array</code>'s elements
   * @return an expression of the same type as <code>array</code>
   */
  Expression updateArray(Expression array, Expression index, Expression newValue);

  /**
   * A variable in the encoding. Creates the variable if it doesn't already
   * exist. If a variable with the same name already exists, it will be returned
   * if <code>fresh</code> is false; a new variable with a mangled name will be
   * created if <code>fresh</code> is true.
   * 
   * @param name
   *          the name of the variable
   * @param type
   *          the type of the variable
   * @param fresh
   *          if true, the variable is guaranteed to be unique in the encoding
   * @return an expression encoding the variable 
   */
  Expression variable(String name, IRType type, boolean fresh) ;
  
  /**
   * The integer constant 0. May be more efficient than
   * <code>integerConstant(0)</code> in some implementations.
   */
  Expression zero() ;
  
  /**
   * The pointer addition of the given expressions. 
   * 
   * @param lhs an pointer-encoded expression
   * @param rhs an integer-encoded expression
   * @return an pointer-encoded expression
   */
  Expression pointerPlus(Expression lhs, Expression rhs) ;
  
  /**
   * The pointer subtraction of the given expressions. 
   * 
   * @param lhs an pointer-encoded expression
   * @param rhs an integer-encoded expression
   * @return an pointer-encoded expression
   */
  Expression pointerMinus(Expression lhs, Expression rhs) ;
  
  /**
   * <code>base <= base + size</code> while <code>+</code>
   * is modular arithmetic in fixed-size bitvector encoding 
   * 
   * @param base
   * @param size must be positive
   * @return
   */
  Expression notOverflow(Expression base, Expression size);
  
  /**
   * Regions <code>[base1, base1 + size1)</code> and <code>[base2, base2 + size2)</code> are
   * disjoint.
   * 
   * @param base1
   * @param size1
   * @param base2
   * @param size2
   * @return
   */
  Expression disjoint(Expression base1, Expression size1, Expression base2, Expression size2);
  
  /**
   * Regions <code>[base1, base1 + size1)</code> and <code>base2</code> are
   * disjoint.
   * 
   * @param base1
   * @param size1
   * @param base2
   * @return
   */
  Expression disjoint(Expression base1, Expression size1, Expression base2);
  
  /**
   * Region <code>[base2, base2 + size2)</code> is within region 
   * <code>[base1, base1 + size1)</code>
   * 
   * @param base1
   * @param size1
   * @param base2
   * @param size2
   * @return
   */
  Expression within(Expression base1, Expression size1, Expression base2, Expression size2);
  
  /**
   * <code>base2</code> is within region <code>[base1, base1 + size1)</code>
   * 
   * @param base1
   * @param size1
   * @param base2
   * @return
   */
  Expression within(Expression base1, Expression size1, Expression base2);

  /**
   * A bound variable in the encoding. Creates the bound variable if it doesn't already
   * exist. If a bound variable with the same name already exists, it will be returned
   * if <code>fresh</code> is false; a new bound variable with a mangled name will be
   * created if <code>fresh</code> is true.
   * 
   * @param name
   *          the name of the bound variable
   * @param type
   *          the type of the bound variable
   * @param fresh
   *          if true, the bound variable is guaranteed to be unique in the encoding
   * @return an expression encoding the bound variable 
   */
	Expression boundVar(String name, IRType type, boolean fresh);

  /**
   * A bound expression in the encoding. Creates the bound expression if it doesn't already
   * exist. If a bound expression with the same name already exists, it will be returned
   * if <code>fresh</code> is false; a new bound expression with a mangled name will be
   * created if <code>fresh</code> is true.
   * 
   * @param name
   *          the name of the bound expression
   * @param type
   *          the type of the bound expression
   * @param fresh
   *          if true, the bound expression is guaranteed to be unique in the encoding
   * @return an expression encoding the bound expression 
   */
	Expression boundExpression(String name, int index, IRType type, boolean fresh);

	/**
	 * Get the unknown expression for <code>type</code>
	 * @param type
	 * @return
	 */
	Expression unknown(xtc.type.Type type);
	
	/**
	 * Convert the type of <code>lhs</code> and <code>rhs</code> with type <code>lhsType
	 * </code> and <code>rhsType</code> for arithmetic computation
	 * @return
	 */
	Pair<Expression, Expression> arithTypeConversion(Expression lhs, Expression rhs,
			Type lhsType, Type rhsType);

	/**
	 * Generate the corresponding rval-binding
	 * @param lvalBinding
	 * @return
	 */
	VariableExpression getRvalBinding(Expression lvalBinding);
}
