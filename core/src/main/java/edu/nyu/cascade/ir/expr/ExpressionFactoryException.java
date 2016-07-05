package edu.nyu.cascade.ir.expr;

import com.google.common.base.Function;
import com.google.common.collect.ComputationException;
import com.google.common.collect.Iterables;

@SuppressWarnings("serial")
public class ExpressionFactoryException extends RuntimeException {
	public static interface ThrowingFunction<F, T> {
		public T apply(F arg) throws ExpressionFactoryException;
	}

	public static <F, T> Iterable<T> wrapIterableTransformation(Iterable<F> args,
			final ThrowingFunction<? super F, ? extends T> f)
			throws ExpressionFactoryException {
		try {
			return Iterables.transform(args, new Function<F, T>() {
				@Override
				public T apply(F arg) {
					try {
						return f.apply(arg);
					} catch (ExpressionFactoryException e) {
						throw new ComputationException(e);
					}
				}
			});
		} catch (ComputationException e) {
			if (e.getCause() instanceof ExpressionFactoryException) {
				throw (ExpressionFactoryException) e.getCause();
			} else {
				throw e;
			}
		}
	}

	public ExpressionFactoryException(String msg) {
		super(msg);
	}

	public ExpressionFactoryException(Throwable cause) {
		super(cause);
	}

	public ExpressionFactoryException(String msg, Throwable cause) {
		super(msg, cause);
	}
}
