package edu.nyu.cascade.prover;

import com.google.common.base.Preconditions;

public class ValidityResult<T> extends QueryResult<ValidityResult.Type> {
	public static enum Type {
		VALID, INVALID, UNKNOWN;
	}

	public static <T> ValidityResult<T> valid(Expression phi) {
		return new ValidityResult<T>(Type.VALID, phi);
	}

	public static <T> ValidityResult<T> valueOf(Type result, Expression phi,
	    Iterable<? extends BooleanExpression> assumptions) {
		Preconditions.checkArgument(!Type.VALID.equals(result));
		return new ValidityResult<T>(result, phi, assumptions);
	}

	public static <T> ValidityResult<T> valueOf(Type result, Expression phi,
	    Iterable<? extends BooleanExpression> assumptions, String reason) {
		Preconditions.checkArgument(!Type.VALID.equals(result));
		return new ValidityResult<T>(result, phi, assumptions, reason);
	}

	private ValidityResult(Type result, Expression phi) {
		super(result, phi);
	}

	private ValidityResult(Type result, Expression phi,
	    Iterable<? extends BooleanExpression> assumptions) {
		super(result, phi, assumptions);
	}

	private ValidityResult(Type result, Expression phi,
	    Iterable<? extends BooleanExpression> assumptions, String reason) {
		super(result, phi, assumptions, reason);
	}

	public boolean isValid() {
		return Type.VALID.equals(getType());
	}

	public boolean isInvalid() {
		return Type.INVALID.equals(getType());
	}

	public boolean isUnknown() {
		return Type.UNKNOWN.equals(getType());
	}
}
