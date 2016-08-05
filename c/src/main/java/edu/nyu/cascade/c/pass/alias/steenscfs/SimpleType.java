package edu.nyu.cascade.c.pass.alias.steenscfs;

class SimpleType extends ValueType {

	private final ECR loc;
	private final ECR func;
	private final Size size;

	private Parent parent;

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("SIMPLE (").append(((ECR) loc
				.findRoot()).getId()).append(", ").append(((ECR) func.findRoot())
						.getId()).append(", ").append(size).append(", ").append(parent)
				.append(')');

		return sb.toString();
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof SimpleType))
			return false;
		SimpleType that = (SimpleType) o;
		if (!loc.equals(that.loc))
			return false;
		if (!func.equals(that.func))
			return false;
		if (!size.equals(that.size))
			return false;
		if (!parent.equals(that.parent))
			return false;
		return true;
	}

	SimpleType(ECR loc, ECR func, Size size, Parent parent) {
		this.loc = loc;
		this.func = func;
		this.size = size;
		this.parent = parent;
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

	ECR getLoc() {
		return loc;
	}

	ECR getFunc() {
		return func;
	}
}
