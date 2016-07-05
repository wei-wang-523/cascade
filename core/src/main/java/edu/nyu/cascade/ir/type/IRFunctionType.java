package edu.nyu.cascade.ir.type;

import java.util.Collection;

public final class IRFunctionType<T extends IRType> extends IRType {

	public static <T extends IRType> IRFunctionType<T> getInstance(
			Collection<IRType> parameterTypes, T returnType) {
		return new IRFunctionType<T>(parameterTypes, returnType);
	}

	private final Collection<IRType> parameterTypes;
	private final T returnType;

	private IRFunctionType(Collection<IRType> parameterTypes, T returnType) {
		this.parameterTypes = parameterTypes;
		this.returnType = returnType;
	}

	public boolean isVoid() {
		return returnType == null;
	}

	@Override
	public Kind getKind() {
		return Kind.FUNCTION;
	}

	public Iterable<IRType> getParameterTypes() {
		return parameterTypes;
	}

	public T getReturnType() {
		return returnType;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Function ");

		if (parameterTypes != null) {
			if (!parameterTypes.isEmpty()) {
				sb.append("(");
				for (IRType paramType : parameterTypes) {
					sb.append(paramType).append(", ");
				}
				int lastIdx = sb.lastIndexOf(",");
				sb.replace(lastIdx, lastIdx + 1, ")");
			} else {
				sb.append("_");
			}
		}

		if (returnType != null) {
			sb.append(" -> ").append(returnType);
		} else {
			sb.append(" -> Void");
		}

		return sb.toString();
	}

	public boolean hasReturnType() {
		return !returnType.getKind().equals(Kind.VOID);
	}
}
