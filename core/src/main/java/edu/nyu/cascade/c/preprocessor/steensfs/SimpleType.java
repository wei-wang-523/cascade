package edu.nyu.cascade.c.preprocessor.steensfs;

class SimpleType extends ValueType {

	private final ECR loc;
	private final ECR func;
	private Parent parent;
	private Size size;
	
	@Override
	ValueTypeKind getKind() {
		return ValueTypeKind.SIMPLE;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("SIMPLE (")
				.append(((ECR) loc.findRoot()).getId())
				.append(" * ")
				.append(loc.getOffset())
				.append(", ")
				.append(((ECR) func.findRoot()).getId())
				.append(", ")
				.append(size)
				.append(", ")
				.append(parent)
				.append(')');
		
		return sb.toString();
	}
	
	SimpleType(ECR loc, ECR func, Size size, Parent parent) {
		this.loc = loc;
		this.func = func;
		this.size = size;
		this.parent = parent;
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
	void setParent(Parent parent) {
		this.parent = parent;
	}

	ECR getLoc() {
		return loc;
	}

	ECR getFunc() {
		return func;
	}
}
