package edu.nyu.cascade.c.pass;

import java.math.BigInteger;

import edu.nyu.cascade.ir.pass.IRVar;
import xtc.type.Type;

public class Value implements Comparable<Value>, IRVar {
	private Type Type;
	private String Name;
	private String Scope;
	private BigInteger ID;
	private static BigInteger nextID = BigInteger.ZERO;

	Value(Type type) {
		ID = nextID;
		Type = type;
		nextID = nextID.add(BigInteger.ONE);
	}

	@Override
	public int compareTo(Value o) {
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

	void setType(Type type) {
		Type = type;
	}

	void setName(String name) {
		Name = name;
	}

	public String getName() {
		return Name;
	}

	boolean hasName() {
		return Name != null;
	}

	@Override
	public String getScopeName() {
		return Scope;
	}

	void setScope(String scope) {
		Scope = scope;
	}

	boolean hasScope() {
		return Scope != null;
	}

	@Override
	public void setProperty(String id, Object o) {
		// TODO Auto-generated method stub

	}

	@Override
	public Object getProperty(String id) {
		// TODO Auto-generated method stub
		return null;
	}

	static void reset() {
		nextID = BigInteger.ZERO;
	}
}
