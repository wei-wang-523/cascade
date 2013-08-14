package edu.nyu.cascade.prover;

import java.util.List;

import xtc.tree.GNode;

import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.Type;

/**
 * Interface for the general expressions that are used in Prior. Each expression
 * is associated with an expression manager that can be obtained with the
 * getExpressionManager() method. Other important properties of the expression
 * are it's kind, type, arity, and children, which can be obtained with the
 * corresponding methods.
 * 
 * @author <a href="mailto:dejan@cs.nyu.edu">Dejan Jovanović</a>
 * @author <a href="mailto:cconway@cs.nyu.edu">Christopher Conway</a>
 */

public interface Expression {
  public static enum Kind {
    /** Boolean AND. Two or more children, all booleans. */
    AND,
    /**
     * Function application. Two or more children: a function and a number of
     * arguments consistent with its arity.
     */
    APPLY,
    /** Indexing an array (e.g., a[i]). Two children: the array and the index. */
    ARRAY_INDEX,
    /**
     * An array literal. One child: an expression of element type defining the 
     * mapping all indexes to elements
     */
    ARRAY_STORE_ALL,
    /**
     * Updating an array element with a new value. Three children: the array,
     * the index of the element, and the new value.
     */
    ARRAY_UPDATE,
    /**
     * Bound
     */
    BOUND,
    /** Bit-wise AND. Two children, both bit-vectors. */
    BV_AND,
    /** Concatenation of two bit-vectors. Two children, both bit-vectors. */
    BV_CONCAT,
    /**
     * Extracting a string of bits from a bit-vector (e.g., b[7:5]). Three
     * children: a bit-vector, the position of the high bit of the sub-string
     * (an integer), and the position of the low bit of the sub-string (an
     * integer).
     */
    BV_EXTRACT,
    /** Bit-wise NAND. Two children, both bit-vectors. */
    BV_NAND,
    /** Bit-wise NOR. Two children, both bit-vectors. */
    BV_NOR,
    /** Bit-wise NOT. One children, a bit-vector. */
    BV_NOT,
    /** Bit-wise OR. Two children, both bit-vectors. */
    BV_OR,
    /** Sign extension of a bit-vector. Two children: a bit vector and a size. */
    BV_SIGN_EXTEND,
    /** Bit-wise XNOR. Two children, both bit-vectors. */
    BV_XNOR,
    /** Bit-wise XOR. Two children, both bit-vectors. */
    BV_XOR,
    /** Bit-wise LSHIFT. Two children, both bit-vectors. */
    BV_LSHIFT,
    /** Bit-wise RSHIFT. Two children, both bit-vectors. */
    BV_RSHIFT,
    /** Bit-wise ZERO extend. Two children, size and a bit-vector. */
    BV_ZERO_EXTEND,
    /** A constant of any type. No children. */
    CONSTANT,
    /**
     * Construction of a datatype value. One or more children: a datatype
     * constructor and a number of arguments consistent with its arity.
     */
    DATATYPE_CONSTRUCT,
    /**
     * Selection of a datatype field. Two children: the selector and a datatype
     * value.
     */
    DATATYPE_SELECT,
    /**
     * Testing a datatype value for its constructor type (e.g., isCons(list)).
     * Two children: the constructor and a datatype value.
     */
    DATATYPE_TEST,
    /** Disequality between values. Two or more children. */
    DISTINCT,
    /** Division. Two children. */
    DIVIDE,
    /** Signed Division. Two children. */
    SDIVIDE,
    /** Equality. Two children. */
    EQUAL,
    /**
     * Existential quantification. Two or more children: the variables to
     * quantify over and, finally, the body (a boolean).
     */
    EXISTS,
    /**
     * Universal quantification. Two or more children: the variables to quantify
     * over and, finally, the body (a boolean).
     */
    FORALL,
    /** Greater than comparison. Two children. */
    GT,
    /** Greater than or equal comparison. Two children. */
    GEQ,
    /** A type predicate 
     * TODO: Should have two children: a type and an expression, but
     * children have to be expressions... ??? */
    HAS_TYPE,
    /**
     * A conditional expression. Three children: a boolean, the value if true,
     * and the value if false.
     */
    IF_THEN_ELSE,
    /** Boolean bi-implication. Two children. */
    IFF,
    /** Boolean implication. Two children. */
    IMPLIES,
    /** Instantiation pattern. one child */
    INST_PATTERN,
    /** Instantiation pattern list, a list of children */
    INST_PATTERN_LIST,
    /**
     * Lambda abstraction (e.g., λx.x+1). Two children: a variable and the body.
     */
    LAMBDA,
    /** Less than comparison. Two children. */
    LT,
    /** Less than or equal comparison. Two children. */
    LEQ,
    /** Subtraction. Two children. */
    MINUS,
    /** Null expression. None child */
    NULL_EXPR,
    /** Modulus. Two children. */
    MOD,
    /** Remainder. Two children. */
    REM,
    /** Signed Remainder. Two children. */
    SREM,
    /** Modular. Two children. */
    MULT,
    /** Boolean NAND. Two children. */
    NAND,
    /** Boolean NOR. Two children. */
    NOR,
    /** Boolean NOT. One child. */
    NOT,
    /** Disequality. Two children. */
    NOT_EQUAL,
    /** Boolean OR. Two or more children. */
    OR,
    /** Addition. Two or more children. */
    PLUS,
    /** Exponentiation. Two children: the base and the exponent. */
    POW,
    /** Rewrite rule. Three children: the BoundVarList, the guard, the rule */
    REWRITE_RULE,
    /** Actual rule. Two/Three children: the head, the body, (the triggers, optional) */
    RR_REWRITE,
    /** Actual rule. Two/Three children: the head, the body, (the triggers, optional) */
    RR_REDUCTION,
    /** Actual rule. Two/Three children: the head, the body, (the triggers, optional) */
    RR_DEDUCTION,
    /**
     * Skolem constant. We don't construct these ourselves, but they may bubble
     * up from the theorem prover. NOTE: A Skolem constant does *not* have kind
     * VARIABLE.
     */
    SKOLEM,
    /**
     * Substition. Three or more children: the original expression, a set of a
     * original variables, and the set of replacement expressions.
     * 
     * NOTE (1): The set of replacement expressions must be the same size as the
     * set of original variables.
     * 
     * NOTE (2): The number of children will always be odd.
     */
    SUBST,
    /** A tuple of values (e.g., (1, 3, 2)). Two or more children. */
    TUPLE,
    /**
     * Updating a tuple element with a new value. Three children: the tuple, the
     * index of the element, and the new value. The new value must have the same
     * type as the old value at same index.
     */
    TUPLE_UPDATE,
    /**
     * Indexing a tuple. Two children: the tuple and the index. The type of t[i]
     * is the type of the i'th element of t.
     */
    TUPLE_INDEX,
    /** A type expression. */
    TYPE,
    /** A record of values (e.g., (1, 3, 2)). Two or more children. */
    RECORD,
    /**
     * Updating a record field with a new value. Three children: the record, the
     * field of the element, and the new value. The new value must have the same
     * type as the old value at same fields.
     */
    RECORD_UPDATE,
    /**
     * Selecting one field of record. Two children: the tuple and the field. .
     */
    RECORD_SELECT,
    /** A type expression. */
    /**
     * A type stub (e.g., a reference to a mutually recursive type, before a
     * call to {@link ExpressionManager#dataTypes}).
     */
    TYPE_STUB,
    /** Uninterpreted expression, zero child */
    UNINTERPRETED,
    /** Unary negation. One child. */
    UNARY_MINUS,
    /**
     * A variable of any type.
     * 
     * NOTE: a Skolem constant is not a variable.
     * */
    VARIABLE,
    /**
     * Variable list
     * 
     * NOTE: a bound variable list
     */
    VARIABLE_LIST,
    /** Boolean XNOR. Two children, both boolean. */
    XNOR,
    /** Boolean XOR. Two children, both boolean. */
    XOR
  };

  /**
   * Coerce the expression to a <code>IBitVectorExpression</code>. Throws an
   * exception if the expression is not of bit vector type.
   */
  BitVectorExpression asBitVector();

  /**
   * Coerce the expression to a <code>IBooleanExpression</code>. Throws an
   * exception if the expression is not of boolean type.
   */
  BooleanExpression asBooleanExpression();

  /**
   * Coerce the expression to a <code>IIntegerExpression</code>. Throws an
   * exception if the expression is not of integer type.
   */
  IntegerExpression asIntegerExpression();

  /**
   * Coerce the expression to a <code>IIntegerVariableExpression</code>. Throws
   * an exception if the expression is not a variable of integer type.
   */
  IntegerVariableExpression asIntegerVariable();

  /**
   * Coerce the expression to a <code>IRationalExpression</code>. Throws an
   * exception if the expression is not of rational type.
   */
  RationalExpression asRationalExpression();

  /**
   * Coerce the expression to a <code>IRationalVariableExpression</code>. Throws
   * an exception if the expression is not a variable of rational type.
   */
  RationalVariableExpression asRationalVariable();
  
  /**
   * Coerce the expression to a <code>FunctionExpression</code>.
   * Throws an exception if the expression is not of function type.
   */
  FunctionExpression asFunctionExpression();

  /**
   * Coerce the expression to a <code>IVariableExpression</code>. Throws an
   * exception if the expression is not a variable.
   */
  VariableExpression asVariable();

  /**
   * Returns an equality expression between this expression and <code>e</code>.
   */
  BooleanExpression eq(Expression e);

  /**
   * Returns the arity (number of children this expression has)
   */
  int getArity();

  /** Get the i'th child of this expression. */
  Expression getChild(int i);

  /**
   * Gets all the children of this expression. If no children are present, the
   * empty list is returned.
   * 
   * @return the list of children
   */
  List<? extends Expression> getChildren();

  /**
   * Get the expression manager responsible for this expression.
   * 
   * @return the expression manager.
   */
  ExpressionManager getExpressionManager();

  /**
   * Returns the kind of this expression (i.e., an element of {@link Kind}).
   */
  Kind getKind();
   
  /** Returns the type of this expression (i.e., a subclass of {@link Type}).
   */
  Type getType();
  
  /** Returns the node of this expression.
   */
  GNode getNode();
  
  /** Returns the function declarator of this expression if its kind is APPLY
   */
  FunctionType getFuncDecl();
  
  /** Set the node of this expression.
   */
  Expression setNode(GNode node);

  /**
   * Returns whether the expression is a constant in it's domain (true, false,
   * 1, 2, ...)
   * 
   * @return true if constant, false otherwise
   */
  boolean isConstant();

  /**
   * Returns whether the expression represents a variable. NOTE: This is not the
   * inverse of isConstant()!
   * */
  boolean isVariable();

  /**
   * Returns a function with this expression as the body, where <code>var</code>
   * is bound as a parameter.
   */
  FunctionExpression lambda(VariableExpression var);
  
  /**
   * Returns a function with this expression as the body, where <code>vars</code>
   * are bound as parameters.
   */
  FunctionExpression lambda(
      Iterable<? extends VariableExpression> vars);

  /**
   * Returns a disequality expression between this expression and <code>e</code>.
   */
  BooleanExpression neq(Expression e);

  Expression subst(Expression oldExpr, Expression newExpr);
  /**
   * Returns a new expression, the result of substituting each expression
   * <code>e</code> in <code>oldExprs</code> for the corresponding expression <code>e'</code>
   * in <code>newExprs</code>.
   */
  Expression subst(Iterable<? extends Expression> oldExprs,
      Iterable<? extends Expression> newExprs);

  ArrayExpression asArray();
  InductiveExpression asInductive();
  TupleExpression asTuple();
  RecordExpression asRecord();
  UninterpretedExpression asUninterpreted();

  boolean isArray();
  boolean isBoolean();
  boolean isInteger();
  boolean isBitVector();
  boolean isFunction();
  boolean isRational();
  boolean isTuple();
  boolean isInductive();
  boolean isRecord();
  boolean isUninterpreted();

}
