package edu.nyu.cascade.ir.expr;

import edu.nyu.cascade.prover.ArrayExpression;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.prover.ExpressionManager;

public interface ArrayEncoding<T extends Expression> {
	/** An instance of the encoding, for given index and element types. */
	public interface Instance<T extends Expression> extends TypeEncoding<T> {
		ArrayExpression toArrayExpression(T array);

		Expression index(T array, Expression index);

		T update(T array, Expression index, Expression elem);

		TypeEncoding<?> getIndexEncoding();

		TypeEncoding<?> getElementEncoding();
	}

	/**
	 * Returns the <code>ExpressionManager</code> object used in the underlying
	 * expression encoding.
	 */
	ExpressionManager getExpressionManager();

	Instance<T> getInstance(TypeEncoding<?> indexEncoding,
			TypeEncoding<?> elementEncoding);

	Expression index(T array, Expression index);

	T update(T array, Expression index, Expression elem);

	boolean isEncodingFor(Expression x);

	T ofExpression(Expression expr);
}
