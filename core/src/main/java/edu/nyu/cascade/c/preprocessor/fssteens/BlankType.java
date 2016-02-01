package edu.nyu.cascade.c.preprocessor.fssteens;

import com.google.common.base.Preconditions;

import edu.nyu.cascade.c.CScopeAnalyzer;
import edu.nyu.cascade.c.CType;
import xtc.type.Type;

public class BlankType extends ValueType {
	
	private final Parent parent;
	private final Type xtcType;
	private final String scopeName;
	private Size size;
	private ECR address;
	
	BlankType(Size size, Parent parent, Type xtcType, String scopeName) {
		this.size = size;
		this.parent = parent;
		this.xtcType = xtcType;
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
				CType.getUnitType(), 
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
}
