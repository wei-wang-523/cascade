package edu.nyu.cascade.prover;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;

import org.apache.commons.cli.Option;

import com.google.common.collect.ImmutableList;

import edu.nyu.cascade.prover.type.ArrayType;
import edu.nyu.cascade.prover.type.BitVectorType;
import edu.nyu.cascade.prover.type.BooleanType;
import edu.nyu.cascade.prover.type.Constructor;
import edu.nyu.cascade.prover.type.FunctionType;
import edu.nyu.cascade.prover.type.InductiveType;
import edu.nyu.cascade.prover.type.IntegerType;
import edu.nyu.cascade.prover.type.RationalType;
import edu.nyu.cascade.prover.type.RecordType;
import edu.nyu.cascade.prover.type.Selector;
import edu.nyu.cascade.prover.type.TupleType;
import edu.nyu.cascade.prover.type.Type;
import edu.nyu.cascade.prover.type.UninterpretedType;

/**
 * Expression manager interface provides the methods to construct expressions. A
 * theorem prover that plugs into Prior should implement an expression manager
 * that can be used with it.
 * 
 * [chris 10/2/2009] TODO: Add a getCapabilities() method, indicating which
 * operations are supported, for concrete implementations that don't have
 * bit-vectors, arrays, or datatypes?
 * 
 * @author <a href="mailto:dejan@cs.nyu.edu">Dejan Jovanović</a>
 * @author <a href="mailto:cconway@cs.nyu.edu">Christopher Conway</a>
 */
public interface ExpressionManager {

	/**
	 * Add a trigger pattern p to quantified expression e. A trigger pattern is a
	 * term or atomic predicate that is a sub-expression of e. The free variables
	 * of p will be used to instantiate the quantified variables of e during query
	 * processing. p will be added to the end of the list of triggers for e, i.e.,
	 * it will be matched last.
	 * 
	 * Concrete implementations of IExpressionManager may ignore triggers.
	 */
	void addTrigger(Expression e, Expression p);

	/**
	 * Create a new Boolean and expression.
	 * 
	 * @param left
	 *          the left operand
	 * @param right
	 *          the right operand
	 * @return the and of left and right
	 */
	BooleanExpression and(Expression left, Expression right);

	/**
	 * Create a new Boolean and expression.
	 * 
	 * @param first
	 *          the first operand
	 * @param rest
	 *          the remaining operands
	 * @return the logical AND of all the operands
	 */
	BooleanExpression and(Expression first, Expression... rest);

	/**
	 * Create a new Boolean AND expression given a list of subexpressions.
	 * 
	 * @param subExpressions
	 *          the list of subexpressions to use
	 * @return the and of left and right
	 */
	BooleanExpression and(Iterable<? extends Expression> subExpressions);

	/**
	 * Create a function expression with parameter <code>arg</code> and function
	 * expression <code>fun</code>
	 */
	Expression applyExpr(Expression fun, Iterable<? extends Expression> args);

	Expression applyExpr(Expression fun, Expression first, Expression... rest);

	/**
	 * Get an array type object given index and element types.
	 * 
	 * @param index
	 *          the index type
	 * @param elem
	 *          the element type
	 * @return an array type
	 */
	ArrayType arrayType(Type index, Type elem);

	ArrayType asArrayType(Type type);

	ArrayType asArrayType(Type indexType, Type elementType);

	BitVectorExpression asBitVector(Expression expression);

	BitVectorType asBitVectorType(Type t);

	BooleanExpression asBooleanExpression(Expression expression);

	FunctionExpression asFunctionExpression(Expression t);

	FunctionType asFunctionType(Type t);

	IntegerExpression asIntegerExpression(Expression expression);

	RationalExpression asRationalExpression(Expression expression);

	TupleType asTupleType(Type t);

	RecordType asRecordType(Type t);

	VariableExpression asVariable(Expression var);

	BoundExpression asBoundExpression(Expression bound);

	/**
	 * Create a bit-vector constant of given size representing the value
	 * <code>n mod 2<sup>size</sup></code>.
	 */
	BitVectorExpression bitVectorConstant(int n, int size);

	/**
	 * Create a bit-vector constant of given size representing the value
	 * <code>n mod 2<sup>size</sup></code>.
	 */
	BitVectorExpression bitVectorConstant(long n, int size);

	/**
	 * Create a bit-vector constant of given size representing the value
	 * <code>n mod 2<sup>size</sup></code>.
	 */
	BitVectorExpression bitVectorConstant(BigInteger n, int size);

	/**
	 * Create a bit-vector constant of the integer value <code>n</code>.
	 */
	BitVectorExpression bitVectorConstant(int n);

	/**
	 * Create a bit-vector constant of the long value <code>n</code>.
	 */
	BitVectorExpression bitVectorConstant(long n);

	/**
	 * Create a bit-vector constant of the big integer value <code>n</code>.
	 */
	BitVectorExpression bitVectorConstant(BigInteger n);

	/**
	 * Create a bit-vector constant given a binary string <code>rep</code>. The
	 * string should use the characters '0' ('\u0030') and '1' ('\u0031') as
	 * binary digits. The size of the returned bit vector will be exactly the
	 * length of rep.
	 */
	BitVectorExpression bitVectorConstant(String rep);

	BitVectorExpression bitVectorOne(int size);

	BitVectorType bitVectorType(int size);

	BitVectorExpression bitVectorZero(int size);

	BitVectorExpression bitwiseAnd(Expression a, Expression b);

	BitVectorExpression bitwiseNand(Expression a, Expression b);

	BitVectorExpression bitwiseNor(Expression a, Expression b);

	BitVectorExpression bitwiseNot(Expression a);

	BitVectorExpression bitwiseOr(Expression a, Expression b);

	BitVectorExpression bitwiseXnor(Expression a, Expression b);

	BitVectorExpression bitwiseXor(Expression a, Expression b);

	/**
	 * Get the Boolean type object.
	 * 
	 * @return the Boolean type
	 */
	BooleanType booleanType();

	/**
	 * Concatenate two bit vectors. The result will be a bit vector with length
	 * <code>left.length + right.length</code>.
	 */
	BitVectorExpression concat(Expression left, Expression right);

	/**
	 * Get the integer expression representing the given constant.
	 * 
	 * @param c
	 *          the constant
	 * @return the expression representing c
	 */
	IntegerExpression constant(int c);

	/**
	 * Get the integer expression representing the given constant.
	 * 
	 * @param c
	 *          the constant
	 * @return the expression representing c
	 */
	IntegerExpression constant(long c);

	/**
	 * Get the integer expression representing the given constant.
	 * 
	 * @param c
	 *          the Big Integer constant
	 * @return the expression representing c
	 */
	IntegerExpression constant(BigInteger c);

	/**
	 * Create an instance of an inductive datatype, using an n-ary value
	 * constructor (where n ≥ 1). The expression will have type
	 * <code>constructor.getType()</code>
	 * 
	 * @param constructor
	 *          the value constructor
	 * @param args
	 *          the remaining arguments to the constructor (maybe none). The
	 *          number of arguments given (including <code>first</code>) must
	 *          match the arity of <code>constructor</code>.
	 * @throws IllegalArgumentException
	 *           if <code>constructor.getArity() != rest.length + 1</code>
	 */

	InductiveExpression construct(Constructor constructor, Expression... args);

	InductiveExpression construct(Constructor constructor,
			Iterable<? extends Expression> args);

	/**
	 * Create a datatype constructor with the given selectors. If
	 * <code>name</code> has been previously used as an identifier, the name will
	 * be mangled. Each selector can only be associated with a single constructor.
	 * The constructor must be associated with a datatype by a subsequent call to
	 * <code>dataType</code> or <code>dataTypes</code>.
	 */
	Constructor constructor(String name, Selector... selectors);

	/**
	 * Create an inductive datatype with the given constructors. If
	 * <code>name</code> has been previously used as an identifier, the name may
	 * be mangled.
	 */
	InductiveType dataType(String name, Constructor... constructors);

	/**
	 * Create a set of mutually recursive datatypes. If any of the names have been
	 * previously used as an identifier, they may be mangled.
	 * 
	 * @param names
	 *          the suggested names of the datatypes
	 * 
	 * @param constructorLists
	 *          lists of constructors associated with each datatype. The number of
	 *          lists must be exactly <code>names.size()</code>.
	 * 
	 * @throws IllegalArgumentException
	 *           if the number of construtor list arguments is not
	 *           <code>names.size()</code>
	 */
	ImmutableList<? extends InductiveType> dataTypes(List<String> names,
			List<? extends Constructor>... constructorLists);

	/**
	 * Create an expression stating that all of the children are pairwise
	 * distinct. I.e., the expression created by
	 * <code>distinctExpression(args)</code> says
	 * <code>∀i≠j. args[i] ≠ args[j]</code>.
	 * 
	 * @param <T>
	 *          the type of the sub-expressions
	 * @param first
	 *          the first argument
	 * @param second
	 *          the second argument
	 * @param rest
	 *          the remainder of the arguments
	 * @return a boolean expression representing the assertion that the arguments
	 *         are pairwise distinct
	 */
	BooleanExpression distinct(Expression first, Expression second,
			Expression... rest);

	/**
	 * Create an expression stating that all of the children are pairwise
	 * distinct. I.e., the expression created by
	 * <code>distinctExpression(args)</code> says
	 * <code>∀i≠j. args[i] ≠ args[j]</code>.
	 * 
	 * @param <T>
	 *          the type of the sub-expressions
	 * @param args
	 *          the arguments
	 * @return a boolean expression representing the assertion that the arguments
	 *         are pairwise distinct
	 */
	BooleanExpression distinct(Iterable<? extends Expression> args);

	/**
	 * Given two integer expression, create the bit-vector expression representing
	 * the ratio of the two.
	 * 
	 * @param numerator
	 *          the numerator of the ratio
	 * @param denominator
	 *          the denominator of the ratio
	 * @return the ratio of numerator and denominator
	 */
	Expression divide(Expression numerator, Expression denominator);

	BitVectorExpression signedDivide(Expression numerator,
			Expression denominator);

	/**
	 * Given two integer expression, create the bit-vector expression representing
	 * the remainder of division
	 * 
	 * @param numerator
	 *          the numerator of the ratio
	 * @param denominator
	 *          the denominator of the ratio
	 * @return the remainder
	 */
	BitVectorExpression rem(Expression numerator, Expression denominator);

	BitVectorExpression signedRem(Expression numerator, Expression denominator);

	/**
	 * Create a new equality expression
	 * 
	 * @param left
	 *          the left operand
	 * @param right
	 *          the right operand
	 * @return the or of left and right
	 */
	BooleanExpression eq(Expression left, Expression right);

	/**
	 * Given a boolean expression and a list of variables, create the existential
	 * quantification of the variables over the body.
	 * 
	 * @param vars
	 *          the variables to quantify out
	 * @param body
	 *          the expression to quantify
	 * @return a new existential expression
	 */

	BooleanExpression exists(Expression var, Expression body);

	BooleanExpression exists(Expression var, Expression body,
			Iterable<? extends Expression> patterns);

	BooleanExpression exists(Expression var, Expression body,
			Iterable<? extends Expression> patterns,
			Iterable<? extends Expression> noPatterns);

	BooleanExpression exists(Expression var1, Expression var2, Expression body);

	BooleanExpression exists(Expression var1, Expression var2, Expression body,
			Iterable<? extends Expression> patterns);

	BooleanExpression exists(Expression var1, Expression var2, Expression body,
			Iterable<? extends Expression> patterns,
			Iterable<? extends Expression> noPatterns);

	BooleanExpression exists(Expression var1, Expression var2, Expression var3,
			Expression body);

	BooleanExpression exists(Expression var1, Expression var2, Expression var3,
			Expression body, Iterable<? extends Expression> patterns);

	BooleanExpression exists(Expression var1, Expression var2, Expression var3,
			Expression body, Iterable<? extends Expression> patterns,
			Iterable<? extends Expression> noPatterns);

	BooleanExpression exists(Iterable<? extends Expression> vars,
			Expression body);

	BooleanExpression exists(Iterable<? extends Expression> vars, Expression body,
			Iterable<? extends Expression> patterns);

	BooleanExpression exists(Iterable<? extends Expression> vars, Expression body,
			Iterable<? extends Expression> patterns,
			Iterable<? extends Expression> noPatterns);

	/**
	 * Get the sub-vector between indices i and j in bitvector b, where i is the
	 * less-significant bit and b the more-significant. The resulting bitvector
	 * will have (j-i)+1 bits. E.g., if <code>b</code> is <code>10110111</code>,
	 * then <code>bitVectorSlice(b,2,6)</code> will return <code>01101</code>.
	 */
	BitVectorExpression extract(Expression bv, int i, int j);

	BooleanExpression ff();

	/**
	 * Given a boolean expression and an Iterable over a set of variables, create
	 * the universal quantification of the variables over the body, possibly using
	 * a collection of trigger patterns as an instantiation heuristic. A trigger
	 * pattern p is a term or atomic predicate that is a sub-expression of e. The
	 * free variables of p will be used to instantiate the quantified variables of
	 * e during query processing. The trigger patterns will matched in the order
	 * they appear in the Iterable.
	 * 
	 * Concrete implementations of IExpressionManager may ignore triggers.
	 * 
	 * @param vars
	 *          the variables to quantify out
	 * @param body
	 *          the expression to quantify
	 * @param patterns
	 *          a collection of trigger patterns
	 * @return a new universal expression
	 */

	BooleanExpression forall(Expression var, Expression body);

	BooleanExpression forall(Expression var, Expression body,
			Iterable<? extends Expression> patterns);

	BooleanExpression forall(Expression var, Expression body,
			Iterable<? extends Expression> patterns,
			Iterable<? extends Expression> noPatterns);

	BooleanExpression forall(Expression var1, Expression var2, Expression body);

	BooleanExpression forall(Expression var1, Expression var2, Expression body,
			Iterable<? extends Expression> patterns);

	BooleanExpression forall(Expression var1, Expression var2, Expression body,
			Iterable<? extends Expression> patterns,
			Iterable<? extends Expression> noPatterns);

	BooleanExpression forall(Expression var1, Expression var2, Expression var3,
			Expression body);

	BooleanExpression forall(Expression var1, Expression var2, Expression var3,
			Expression body, Iterable<? extends Expression> patterns);

	BooleanExpression forall(Expression var1, Expression var2, Expression var3,
			Expression body, Iterable<? extends Expression> patterns,
			Iterable<? extends Expression> noPatterns);

	BooleanExpression forall(Iterable<? extends Expression> vars,
			Expression body);

	BooleanExpression forall(Iterable<? extends Expression> vars, Expression body,
			Iterable<? extends Expression> patterns);

	BooleanExpression forall(Iterable<? extends Expression> vars, Expression body,
			Iterable<? extends Expression> patterns,
			Iterable<? extends Expression> noPatterns);

	/**
	 * Wrap the arg into a rewrite rule axiom
	 * 
	 * @param arg
	 * @return the rewrite rule
	 */
	BooleanExpression rewriteRule(Iterable<? extends Expression> vars,
			Expression guard, Expression rule);

	/**
	 * Compose rewrite rule
	 */

	BooleanExpression rrRewrite(Expression head, Expression body,
			Iterable<? extends Expression> triggers);

	BooleanExpression rrRewrite(Expression head, Expression body);

	BooleanExpression rrReduction(Expression head, Expression body,
			Iterable<? extends Expression> triggers);

	BooleanExpression rrReduction(Expression head, Expression body);

	BooleanExpression rrDeduction(Expression head, Expression body,
			Iterable<? extends Expression> triggers);

	BooleanExpression rrDeduction(Expression head, Expression body);

	/**
	 * Get an n-ary function type object given a collection of domain types and a
	 * range type in an Iterable.
	 * 
	 * @param args
	 *          an Iterable over the domain types of the function arguments (must
	 *          have at least 2 elements)
	 * @return an function type
	 */
	/*
	 * FunctionType functionType( Iterable<? extends Type> args);
	 */

	/**
	 * Get an n-ary function type object given a collection of domain types and a
	 * range type.
	 * 
	 * @param args
	 *          an Iterable over the domain types of the function arguments (must
	 *          have at least 1 element)
	 * @param range
	 *          the result type
	 * @return an function type
	 */
	FunctionType functionType(Iterable<? extends Type> args, Type range);

	FunctionType functionType(Type argType1, Type argType2, Type... rest);

	FunctionType functionType(Type argType, Type range);

	FunctionExpression functionDeclarator(String name, FunctionType functionType,
			boolean fresh);

	/**
	 * Create a new greater than or equal expression.
	 */
	BooleanExpression greaterThanOrEqual(Expression left, Expression right);

	/**
	 * Create a new signed greater than or equal expression.
	 */
	BooleanExpression signedGreaterThanOrEqual(Expression left, Expression right);

	/**
	 * Returns a list of implementation-specific options, including options for
	 * the underlying theorem prover.
	 */
	ImmutableList<Option> getOptions();

	/**
	 * Returns the responsible theorem prover.
	 * 
	 * @return the theorem prover
	 */
	TheoremProver getTheoremProver();

	/**
	 * Create a new greater than expression
	 */
	BooleanExpression greaterThan(Expression lhs, Expression rhs);

	/**
	 * Create a new signed greater than expression
	 */
	BooleanExpression signedGreaterThan(Expression lhs, Expression rhs);

	/**
	 * Create a new Boolean equivalence expression
	 * 
	 * @param left
	 *          the left operand
	 * @param right
	 *          the right operand
	 * @return the or of left and right
	 */
	BooleanExpression iff(Expression left, Expression right);

	Expression ifThenElse(Expression cond, Expression tt, Expression ff);

	/**
	 * Create a new Boolean implication expression
	 * 
	 * @param left
	 *          the left operand
	 * @param right
	 *          the right operand
	 * @return the or of left and right
	 */
	BooleanExpression implies(Expression left, Expression right);

	/**
	 * Create a new array index expression (e.g., <code>a[i]</code>) given an
	 * array and an index value.
	 * 
	 * @param array
	 *          an expression of type <code>(a,b) array</code>
	 * @param index
	 *          an expression of type <code>a</code>
	 * @return the expression <code>array[index]</code>, of type <code>b</code>
	 */
	Expression index(Expression array, Expression index);

	Expression index(Expression tuple, int index);

	InductiveType inductiveType(String name);

	/**
	 * Get the integer type object.
	 * 
	 * @return the integer type
	 */
	IntegerType integerType();

	/**
	 * Create a new less than or equal expression
	 */
	BooleanExpression lessThanOrEqual(Expression left, Expression right);

	/**
	 * Create a new signed less than or equal expression
	 */
	BooleanExpression signedLessThanOrEqual(Expression left, Expression right);

	/**
	 * Create a new less than expression
	 */
	BooleanExpression lessThan(Expression left, Expression right);

	/**
	 * Create a new signed less than expression
	 */
	BooleanExpression signedLessThan(Expression left, Expression right);

	BitVectorExpression bitVectorMinus(Expression a, Expression b);

	/**
	 * Give two integer expressions, create a new integer expression representing
	 * their difference.
	 * 
	 * @param expression
	 *          the first operand
	 * @param expression2
	 *          the second operand
	 * @return difference of left and right
	 */
	Expression minus(Expression expression, Expression expression2);

	/**
	 * Given two integer expression, create a new integer expression representing
	 * the multiplication of the two
	 * 
	 * @param left
	 *          the first operand
	 * @param right
	 *          the second operand
	 * @return multiplication expression of left and right
	 */
	Expression mult(Expression left, Expression right);

	/**
	 * Given a list of integer expressions, create a new integer expression
	 * representing the multiplication.
	 * 
	 * @param children
	 *          the expressions to be multiplied
	 * @return the multiplication expression of the list
	 */
	Expression mult(List<? extends Expression> children);

	/**
	 * Create a new unary minus expression, i.e. given an integer expression e,
	 * create the integer expression for -(e).
	 * 
	 * @param e
	 *          the expression
	 * @return the negation of the expression
	 */
	Expression negate(Expression e);

	IntegerExpression negativeOne();

	BooleanExpression neq(Expression arg0, Expression arg1);

	/**
	 * Create a new Boolean not expression
	 * 
	 * @param expr
	 *          the sub-expression
	 * @return the or of left and right
	 */
	BooleanExpression not(Expression expr);

	IntegerExpression one();

	BooleanExpression or(Expression... subExpressions);

	/**
	 * Create a new Boolean or expression
	 * 
	 * @param left
	 *          the left operand
	 * @param right
	 *          the right operand
	 * @return the or of left and right
	 */
	BooleanExpression or(Expression left, Expression right);

	/**
	 * Create a new Boolean or expression given a list of subexpressions.
	 * 
	 * @param subExpressions
	 *          the list of subexpressions to use
	 * @return the and of left and right
	 */
	BooleanExpression or(Iterable<? extends Expression> subExpressions);

	/**
	 * Given two integer expressions create a new integer expression representing
	 * their sum.
	 * 
	 * @param left
	 *          the left summand
	 * @param right
	 *          the right summand
	 * @return the sum of given expressions
	 */
	Expression plus(Expression left, Expression right);

	Expression plus(Expression first, Expression... rest);

	BitVectorExpression bitVectorPlus(int size, Expression first,
			Expression... rest);

	BitVectorExpression bitVectorPlus(int size,
			Iterable<? extends Expression> args);

	/**
	 * Given a list of integer expressions, create a new integer expression
	 * representing their sum. The <code>Iterable</code> must have at least one
	 * element.
	 * 
	 * @param children
	 *          the summand to be summed
	 * @return the sum of the given expressions
	 */
	Expression plus(Iterable<? extends Expression> children);

	Expression pow(Expression x, Expression n);

	/**
	 * Get the rational constant represented by the given numerator and
	 * denominator.
	 * 
	 * @param numerator
	 *          the numerator of the constant
	 * @param denominator
	 *          the denominator of the constant
	 * @return the rational object denominator/numerator
	 */
	RationalExpression rationalConstant(int numerator, int denominator);

	/**
	 * Get the rational type object.
	 * 
	 * @return the rational type
	 */
	RationalType rationalType();

	RationalExpression ratOne();

	RationalExpression ratZero();

	Expression select(Selector selector, Expression val);

	/**
	 * Create a datatype selector of the given type. If <code>name</code> has been
	 * previously used as an identifier, the name may be mangled. The selector
	 * must be associated with a datatype constructor by a subsequent call to
	 * <code>constructor</code>.
	 */
	Selector selector(String name, Type type);

	Selector selector(String name, Type type, int ref);

	/**
	 * Set implementation-specific preferences, possibly by requesting information
	 * from <code>edu.nyu.cascade.util.Preferences</code>. Calls
	 * <code>processOptions</code> on the underlying theorem prover as well.
	 * 
	 */
	void setPreferences();

	/**
	 * Add a collection of triggers patterns to quantified expression e. A trigger
	 * pattern p is a term or atomic predicate that is a sub-expression of e. The
	 * free variables of p will be used to instantiate the quantified variables of
	 * e during query processing. The trigger patterns will matched in the order
	 * they appear in the Iterable.
	 * 
	 * Concrete implementations of IExpressionManager may ignore triggers.
	 */
	void setTriggers(Expression e, Iterable<? extends Expression> triggers);

	BitVectorExpression signedExtend(int size, Expression bv);

	/**
	 * Substitute each <code>oldExpr</code> for <code>newExpr</code> in
	 * <code>e</code>. <code>oldExpr</code> and <code>newExpr</code> must have the
	 * same number of elements.
	 */
	Expression subst(Expression e, Iterable<? extends Expression> oldExprs,
			Iterable<? extends Expression> newExprs);

	BooleanExpression testConstructor(Constructor constructor, Expression val);

	BooleanExpression tt();

	TupleExpression tuple(Type type, Expression first, Expression... rest);

	TupleExpression tuple(Type type, Iterable<? extends Expression> elements);

	TupleType tupleType(String tname, Iterable<? extends Type> elementTypes);

	TupleType tupleType(String tname, Type firstType, Type... elementTypes);

	RecordExpression record(Type type, Iterable<? extends Expression> args);

	RecordExpression record(Type type, Expression arg);

	RecordExpression record(Type type, Expression first, Expression... rest);

	RecordType recordType(String tname, Iterable<String> names,
			Iterable<? extends Type> elementTypes);

	RecordType recordType(String tname, String name, Type elementType);

	RecordType recordType(String tname);

	UninterpretedType uninterpretedType(String name);

	/**
	 * Create a new array update expression (e.g., <code>a[i <- e]</code>) given
	 * an array, an index value, and an element value.
	 * 
	 * @param array
	 *          an expression of type <code>(a,b) array</code>
	 * @param index
	 *          an expression of type <code>a</code>
	 * @param value
	 *          an expression of type <code>b</code>
	 * @return an array update expression, of type <code>(a,b) array</code>
	 */
	ArrayExpression update(Expression array, Expression index, Expression value);

	TupleExpression update(Expression tuple, int i, Expression val);

	RecordExpression update(Expression record, String fieldName, Expression val);

	/**
	 * Create a new variable of the given type. If <code>fresh</code> is true and
	 * a variable of the same name has been previously created by this expression
	 * manager, the name may be mangled to ensure uniqueness.
	 */
	VariableExpression variable(String name, Type type, boolean fresh);

	/**
	 * Create a new bound variable of the given type. If <code>fresh</code> is
	 * true and a variable of the same name has been previously created by this
	 * expression manager, the name may be mangled to ensure uniqueness.
	 */
	Expression boundVar(String name, Type type, boolean fresh);

	Expression boundExpression(String name, int i, Type type, boolean fresh);

	/**
	 * Create a new Boolean xor expression
	 * 
	 * @param left
	 *          the left operand
	 * @param right
	 *          the right operand
	 * @return the xor of given expressions
	 */
	BooleanExpression xor(Expression left, Expression right);

	IntegerExpression zero();

	BitVectorExpression zeroExtend(int size, Expression bv);

	BitVectorExpression bitVectorPlus(int size, Expression left,
			Expression right);

	BitVectorExpression bitVectorMult(int size, Expression left,
			Expression right);

	TupleExpression asTuple(Expression e);

	RecordExpression asRecord(Expression e);

	InductiveExpression asInductive(Expression e);

	UninterpretedExpression asUninterpreted(Expression e);

	ArrayExpression asArray(Expression e);

	/**
	 * Create array expression to have all cells to be expr
	 * 
	 * @param expr
	 * @param type
	 * @return the initialized array expression
	 */
	ArrayExpression storeAll(Expression expr, Type type);

	/**
	 * Get a integer value of a constant expression
	 * 
	 * @param expr
	 */
	int valueOfIntegerConstant(Expression expr);

	/**
	 * Get a boolean value of a constant expression
	 * 
	 * @param expr
	 */
	boolean valueOfBooleanConstant(Expression expr);

	/**
	 * Create a lambda expression
	 * 
	 * @param arg
	 * @param body
	 * @return
	 */
	FunctionExpression lambda(Expression arg, Expression body);

	/**
	 * Create a lambda expression
	 * 
	 * @param args
	 * @param body
	 * @return
	 */
	FunctionExpression lambda(Collection<Expression> args, Expression body);

	/**
	 * Clear the static fields.
	 */
	void reset();
}
