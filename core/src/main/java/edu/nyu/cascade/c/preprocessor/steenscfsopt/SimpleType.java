package edu.nyu.cascade.c.preprocessor.steenscfsopt;

class SimpleType extends ValueType {

	private final ECR loc;
	private final ECR func;
	private final Size size;
	
	private Parent parent;
	private boolean op;
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("SIMPLE (")
				.append(((ECR) loc.findRoot()).getId())
				.append(", ")
				.append(((ECR) func.findRoot()).getId())
				.append(", ")
				.append(size)
				.append(", ")
				.append(parent)
				.append(", ")
				.append(op)
				.append(')');
		
		return sb.toString();
	}
	
	@Override
	public boolean equals(Object o) {
		if(!(o instanceof SimpleType)) return false;
		SimpleType that = (SimpleType) o;
		if(!loc.equals(that.loc)) return false;
		if(!func.equals(that.func)) return false;
		if(!size.equals(that.size)) return false;
		if(!parent.equals(that.parent)) return false;
		if(op != that.op) return false;
		return true;
	}
	
	SimpleType(ECR loc, ECR func, Size size, Parent parent, boolean op) {
		this.loc = loc;
		this.func = func;
		this.size = size;
		this.parent = parent;
		this.op = op;
	}

	@Override
	ValueTypeKind getKind() {
		return ValueTypeKind.SIMPLE;
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
	void setParent(Parent parent) {
		this.parent = parent;
	}

	@Override
	boolean hasOpTag() {
		return op;
	}

	@Override
	void enableOpTag() {
		op = true;
	}

	ECR getLoc() {
		return loc;
	}

	ECR getFunc() {
		return func;
	}
}
