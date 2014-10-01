package edu.nyu.cascade.c.preprocessor.steensgaard;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

abstract class ValueType {
  
	enum ValueTypeKind {
    REF,
    LAMBDA,
    BOTTOM
  };
  
  private ECR address;

	static ValueType bottom() {
  	return new BottomType();
  }
  
  static ValueType lam(ECR ret, ECR...args) {
    return new LambdaType(Lists.asList(ret, args));
  }
  
  static ValueType ref(ECR location, ECR function, xtc.type.Type type, String scopeName) {
    return new RefType(location, function, type, scopeName);
  }  

	abstract ValueTypeKind getKind();
	
	ECR getAddress() {
		return address;
	}
	
	void setAddress(ECR addr) {
		address = addr;
	}
	
	LambdaType asLambda() {
		Preconditions.checkArgument(isLambda());
		return (LambdaType) this;
	}
	
	boolean isLambda() {
		return getKind().equals(ValueTypeKind.LAMBDA);
	}
	
	RefType asRef() {
		Preconditions.checkArgument(isRef());
		return (RefType) this;
	}

	boolean isRef() {
	  return getKind().equals(ValueTypeKind.REF);
  }
	
	BottomType asBot() {
		Preconditions.checkArgument(isBot());
		return (BottomType) this;
	}
	
	boolean isBot() {
		return getKind().equals(ValueTypeKind.BOTTOM);
	}
}
