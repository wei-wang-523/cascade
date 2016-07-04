package edu.nyu.cascade.ir.type;

public final class IRVoidType extends IRType {
	private static final IRVoidType singleton = new IRVoidType();

	public static IRVoidType getInstance() {
		return singleton;
	}

	private IRVoidType() {
	}

	@Override
	public String toString() {
		return "void";
	}

	@Override
	public Kind getKind() {
		return Kind.VOID;
	}

}
