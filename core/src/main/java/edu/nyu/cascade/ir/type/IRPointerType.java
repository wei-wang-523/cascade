package edu.nyu.cascade.ir.type;

public final class IRPointerType extends IRType {
	private static final IRPointerType singleton = new IRPointerType();

	public static IRPointerType getInstance() {
		return singleton;
	}

	private IRPointerType() {
	}

	@Override
	public Kind getKind() {
		return Kind.POINTER;
	}

	@Override
	public String toString() {
		return "pointer";
	}
}
