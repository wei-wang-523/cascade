package edu.nyu.cascade.c;

import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.ValidityResult;
import edu.nyu.cascade.util.IOUtils;

public class SafeResult {
	enum SafeResultType {
		TRUE, FALSE, UNKNOWN
	}

	private final SafeResultType type;
	private String failReason;

	private SafeResult(SafeResultType _type) {
		type = _type;
	}

	public static SafeResult valueOf(ValidityResult<?> result) {
		switch (result.getType()) {
		case INVALID:
			return new SafeResult(SafeResultType.FALSE);
		case UNKNOWN:
			return new SafeResult(SafeResultType.UNKNOWN);
		default:
			return new SafeResult(SafeResultType.TRUE);
		}
	}

	public static SafeResult valid() {
		return new SafeResult(SafeResultType.TRUE);
	}

	public static SafeResult invalid() {
		return new SafeResult(SafeResultType.FALSE);
	}

	public static SafeResult unknown(String unknownReason) {
		SafeResult res = new SafeResult(SafeResultType.UNKNOWN);
		if (IOUtils.debugEnabled()) {
			res.setFailReason(unknownReason);
		}
		return res;
	}

	public static SafeResult valueOf(SatResult<?> result) {
		switch (result.getType()) {
		case SAT:
			return new SafeResult(SafeResultType.FALSE);
		case UNKNOWN:
			return new SafeResult(SafeResultType.UNKNOWN);
		default:
			return new SafeResult(SafeResultType.TRUE);
		}
	}

	public void setFailReason(String reason) {
		failReason = reason;
	}

	public boolean isSafe() {
		return type.equals(SafeResultType.TRUE);
	}

	public boolean isUnsafe() {
		return type.equals(SafeResultType.FALSE);
	}

	public boolean isUnknown() {
		return type.equals(SafeResultType.UNKNOWN);
	}

	public String getFailReason() {
		return failReason;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append(type);
		if (failReason != null)
			sb.append('(').append(failReason).append(')');
		return sb.toString();
	}
}
