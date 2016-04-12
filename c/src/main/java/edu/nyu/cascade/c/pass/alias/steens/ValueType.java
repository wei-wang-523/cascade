package edu.nyu.cascade.c.pass.alias.steens;

import com.google.common.base.Preconditions;

abstract class ValueType {
  
	enum ValueTypeKind {
    REF,
    LAMBDA,
    BOTTOM
  };

	static ValueType bottom() {
  	return new BottomType();
  }
  
  static ValueType lam(ECR ret, ECR...args) {
    return new LambdaType(ret, args);
  }
  
  static ValueType ref(ECR location, ECR function) {
    return new RefType(location, function);
  }  

	abstract ValueTypeKind getKind();
	
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
