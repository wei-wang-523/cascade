package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.BooleanExpression;

public interface RationalEncoding<T extends Expression> extends
		TypeEncoding<T> {

	BooleanExpression gt(T lhs, T rhs);

	BooleanExpression geq(T lhs, T rhs);

	BooleanExpression lt(T lhs, T rhs);

	BooleanExpression leq(T lhs, T rhs);

	/** Returns a rational expression representing the constant <code>c</code>. */
	T constant(int numerator, int denominator);

	T plus(T lhs, T rhs);

	T minus(T lhs, T rhs);

	T mult(T lhs, T rhs);

	T divide(T lhs, T rhs);

	T pow(T lhs, T rhs);

	T one();

	T zero();
}
