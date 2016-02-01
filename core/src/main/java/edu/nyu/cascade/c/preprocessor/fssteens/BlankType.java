package edu.nyu.cascade.c.preprocessor.fssteens;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CScopeAnalyzer;

public class BlankType extends ValueType {
	
	private final Parent parent;
	private final String scopeName;
	private Size size;
	private ECR address;
	
	BlankType(Size size, Parent parent, String scopeName) {
		this.size = size;
		this.parent = parent;
		this.scopeName = scopeName;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("BLANK (")
				.append(size)
				.append(", ")
				.append(parent)
				.append(')');
		return sb.toString();
	}

	/**
	 * Get Blank(T, {})
	 * @return
	 */
	static BlankType getTop() {
		return new BlankType(
				Size.getTop(), 
				Parent.getEmpty(),
				CScopeAnalyzer.getRootScopeName());
	}
	
	@Override
	ValueTypeKind getKind() {
		return ValueTypeKind.BLANK;
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
