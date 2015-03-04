package edu.nyu.cascade.c;

import edu.nyu.cascade.prover.SatResult;
import edu.nyu.cascade.prover.ValidityResult;

public class SafeResult {
	enum SafeResultType {
		SAFE,
		UNSAFE,
		UNKNOWN
	}
	
	private final SafeResultType type;
	private String failReason;
	
	private SafeResult(SafeResultType _type) {
		type = _type;
	}
	
	public static SafeResult valueOf(ValidityResult<?> result) {
		switch(result.getType()) {
		case INVALID:
			return new SafeResult(SafeResultType.UNSAFE);
		case UNKNOWN:
			return new SafeResult(SafeResultType.UNKNOWN);
		default:
			return new SafeResult(SafeResultType.SAFE);
		}
	}
	
	public static SafeResult valid() {
		return new SafeResult(SafeResultType.SAFE);
	}
	
	public static SafeResult unknown(String unknownReason) {
		SafeResult res = new SafeResult(SafeResultType.UNKNOWN);
		res.setFailReason(unknownReason);
		return res;
	}
	
	public static SafeResult valueOf(SatResult<?> result) {
		switch(result.getType()) {
		case SAT:
			return new SafeResult(SafeResultType.UNSAFE);
		case UNKNOWN:
			return new SafeResult(SafeResultType.UNKNOWN);
		default:
			return new SafeResult(SafeResultType.SAFE);
		}
	}
	
	public void setFailReason(String reason) {
		failReason = reason;
	}
	
	public boolean isSafe() {
		return type.equals(SafeResultType.SAFE);
	}
	
	public boolean isUnsafe() {
		return type.equals(SafeResultType.UNSAFE);
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
		if(failReason != null) sb.append('(').append(failReason).append(')');
		return sb.toString();
	}
}
