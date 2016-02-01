package edu.nyu.cascade.c.preprocessor.fssteens;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.util.Pair;

public class ObjectType extends ValueType {

	private final Pair<ECR, Offset> loc;
	private final Function func;
	private final Parent parent;
	private final String scopeName;
	private ECR address;
	private Size size;
	
	@Override
	ValueTypeKind getKind() {
		return ValueTypeKind.OBJECT;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("OBJECT (")
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
	
	ObjectType(ECR base, Offset offset, Function func, Size size, Parent parent, String scopeName) {
		this.loc = Pair.of(base, offset);
		this.func = func;
		this.size = size;
		this.parent = parent;
		this.scopeName = scopeName;
	}
	
	Pair<ECR, Offset> getLoc() {
		return loc;
	}
	
	Function getFunc() {
		return func;
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
	void setAddress(ECR address) {
		Preconditions.checkArgument(this.address == null);
		this.address = address;
	}
	
	@Override
	ECR getAddress() {
		return address;
	}
}
