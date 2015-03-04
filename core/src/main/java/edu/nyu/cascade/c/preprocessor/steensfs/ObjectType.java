package edu.nyu.cascade.c.preprocessor.steensfs;

class ObjectType extends ValueType {

	private final ECR loc;
	private final ECR func;
	private Parent parent;
	private Size size;
	
	@Override
	ValueTypeKind getKind() {
		return ValueTypeKind.OBJECT;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("OBJECT (")
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
	
	ObjectType(ECR loc, ECR func, Size size, Parent parent) {
		this.loc = loc;
		this.func = func;
		this.size = size;
		this.parent = parent;
	}
	
	ECR getLoc() {
		return loc;
	}
	
	ECR getFunc() {
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
	void setParent(Parent parent) {
		this.parent = parent;
	}
}
