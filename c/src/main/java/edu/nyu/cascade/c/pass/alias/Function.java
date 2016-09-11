package edu.nyu.cascade.c.pass.alias;

import java.math.BigInteger;
import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import xtc.Constants;
import xtc.type.Type;

public class Function<T> implements Comparable<Function<T>> {
	private Type Type;
	private String Name;
	private String Scope;
	private BigInteger ID;
	private static BigInteger nextID = BigInteger.ZERO;
	private List<T> Args;
	private List<T> VarArgs;
	private T Result;

	public Function(String funcID, String funcScope, Type funcType) {
		Name = funcID;
		ID = nextID;
		Type = funcType;
		Scope = funcScope;
		nextID = nextID.add(BigInteger.ONE);
		Args = Lists.newArrayList();
		VarArgs = Lists.newArrayList();
	}

	@Override
	public int compareTo(Function<T> o) {
		return ID.compareTo(o.ID);
	}

	@Override
	public String toString() {
		if (Name == null || Scope == null)
			return "";
		else
			return Scope + ", " + Name;
	}

	public Type getType() {
		return Type;
	}

	String getName() {
		return Name;
	}

	public String getScopeName() {
		return Scope;
	}

	public T getArgument(int i) {
		Preconditions.checkElementIndex(i, Args.size());
		return Args.get(i);
	}

	public boolean hasVarArgument(int i) {
		return i < VarArgs.size();
	}

	T getVarArgument(int i) {
		Preconditions.checkElementIndex(i, VarArgs.size());
		return VarArgs.get(i);
	}

	public void addArgument(T arg) {
		Args.add(arg);
	}

	public void addVarArgument(T arg) {
		VarArgs.add(arg);
	}

	public void setResult(T res) {
		Result = res;
	}

	public T getResult() {
		return Result;
	}

	public boolean isDeclaration() {
		return !getType().hasAttribute(Constants.ATT_DEFINED);
	}
}
