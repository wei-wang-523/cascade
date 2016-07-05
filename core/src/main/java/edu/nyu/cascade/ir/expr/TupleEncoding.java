package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;
import edu.nyu.cascade.prover.TupleExpression;

public interface TupleEncoding<T extends Expression> {
	/** An instance of the encoding, for given index and element types. */
	public interface Instance<T extends Expression> extends TypeEncoding<T> {
		TupleExpression toTupleExpression(T array);

		Expression index(T tuple, int index);

		T update(T tuple, int index, Expression elem);

		Iterable<TypeEncoding<?>> getElementEncodings();

		String getName();
	}

	/**
	 * Returns the <code>ExpressionManager</code> object used in the underlying
	 * expression encoding.
	 */
	ExpressionManager getExpressionManager();

	Instance<T> getInstance(String name,
			Iterable<TypeEncoding<?>> elementEncodings);

	Instance<T> getInstance(String name, TypeEncoding<?>... elementEncodings);

	Expression index(T tuple, int index);

	T update(T tuple, int index, Expression elem);

	boolean isEncodingFor(Expression x);

	T ofExpression(Expression expr);
}
