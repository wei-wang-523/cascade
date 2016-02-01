package edu.nyu.cascade.c.preprocessor.fssteens;

import com.google.common.base.Preconditions;

import xtc.type.Type;
import edu.nyu.cascade.util.Pair;

class SimpleType extends ValueType {

	private final Pair<ECR, Offset> loc;
	private final Function func;
	private final Parent parent;
	private final Type xtcType;
	private final String scopeName;
	private Size size;
	private ECR address;
	
	@Override
	ValueTypeKind getKind() {
		return ValueTypeKind.SIMPLE;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("SIMPLE (")
				.append(((ECR) loc.fst().findRoot()).getId())
				.append(" * ")
				.append(loc.snd())
				.append(", ")
				.append(func)
				.append(", ")
				.append(size)
				.append(", ")
				.append(parent)
				.append(')');
		
		return sb.toString();
	}
	
	SimpleType(ECR base, Offset offset, Function func, Size size, Parent parent, Type xtcType, String scopeName) {
		this.loc = Pair.of(base, offset);
		this.func = func;
		this.size = size;
		this.parent = parent;
		this.xtcType = xtcType;
		this.scopeName = scopeName;
	}
	
	@Override
	void setSize(Size size) {
		this.size = size;
	}

	@Override
	Size getSize() {
		return size;
	}

	@Override
	Parent getParent() {
		return parent;
	}
	
	@Override
	String getScopeName() {
		return scopeName;
	}

	@Override
	Type getXtcType() {
		return xtcType;
	}

	@Override
	void setAddress(ECR address) {
		Preconditions.checkArgument(this.address == null);
		this.address = address;
	}
	
	@Override
	ECR getAddress() {
		return address;
	}

	Pair<ECR, Offset> getLoc() {
		return loc;
	}

	Function getFunc() {
		return func;
	}
}
