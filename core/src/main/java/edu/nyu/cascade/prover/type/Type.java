package edu.nyu.cascade.prover.type;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;

public interface Type {

	/**
	 * Domain types.
	 * 
	 * @author dejan
	 */
	public enum DomainType {
		BOOLEAN, INTEGER, INTEGER_RANGE, RATIONAL, RATIONAL_RANGE, BITVECTOR, ARRAY, LIST, FUNCTION, DATATYPE, TUPLE, RECORD, UNINTERPRETED
	}

	/**
	 * Returns the type of the domain.
	 * 
	 * @return the type
	 */
	public DomainType getDomainType();

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

	boolean isAddableType();

	AddableType asAddableType();

	boolean isComparableType();

	ComparableType asComparableType();

	boolean isScalarType();

	ScalarType asScalarType();

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
