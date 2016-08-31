package edu.nyu.cascade.c.pass.alias.steenscfs;

import java.math.BigInteger;
import java.util.List;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import xtc.Constants;
import xtc.type.Type;

class CFSFunction implements Comparable<CFSFunction> {
	private Type Type;
	private String Name;
	private String Scope;
	private BigInteger ID;
	private static BigInteger nextID = BigInteger.ZERO;
	private List<ECR> Args;
	private List<ECR> VarArgs;
	private ECR Result;

	CFSFunction(String funcID, String funcScope, Type funcType) {
		Name = funcID;
		ID = nextID;
		Type = funcType;
		Scope = funcScope;
		nextID = nextID.add(BigInteger.ONE);
		Args = Lists.newArrayList();
		VarArgs = Lists.newArrayList();
	}
	
	@Override
	public int compareTo(CFSFunction o) {
		return ID.compareTo(o.ID);
	}

	@Override
	public String toString() {
		if (Name == null || Scope == null)
			return "";
		else
			return Scope + ", " + Name;
	}

	Type getType() {
		return Type;
	}

	String getName() {
		return Name;
	}

	public String getScopeName() {
		return Scope;
	}

	ECR getArgument(int i) {
		Preconditions.checkElementIndex(i, Args.size());
		return Args.get(i);
	}
	
	boolean hasVarArgument(int i) {
		return i < VarArgs.size();
	}
	
	ECR getVarArgument(int i) {
		Preconditions.checkElementIndex(i, VarArgs.size());
		return VarArgs.get(i);
	}
	
	void addArgument(ECR arg) {
		Args.add(arg);
	}
	
	void addVarArgument(ECR arg) {
		VarArgs.add(arg);
	}
	
	void setResult(ECR res) {
		Result = res;
	}
	
	ECR getResult() {
		return Result;
	}
	
	boolean isDeclaration() {
		return !getType().hasAttribute(Constants.ATT_DEFINED);
	}
}
