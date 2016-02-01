package edu.nyu.cascade.c.preprocessor.fssteens;

import com.google.common.base.Preconditions;

class BottomType extends ValueType {
	private ECR address;
	
	@Override
	ValueTypeKind getKind() {
		return ValueTypeKind.BOTTOM;
	}
	
	@Override
	public String toString() {
		return new StringBuilder().append("BOT").toString();
	}
	
	@Override
	void setSize(Size size) {
		throw new UnsupportedOperationException("Cannot set size for bottom type");
	}

	@Override
	Size getSize() {
		return Size.createZero();
	}

	@Override
  Parent getParent() {
	  return Parent.getEmpty();
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
	
	@Override
  String getScopeName() {
		return null;
  }
}
