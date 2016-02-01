package edu.nyu.cascade.c.preprocessor.steensgaard;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.Lists;

import edu.nyu.cascade.util.EqualsUtil;

class LambdaType extends ValueType {
	
	private final List<ECR> operands;
	
	LambdaType(Collection<ECR> operands) {
		this.operands = Lists.newArrayList(operands);
	}
	
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder().append("LAM ( ");
    for(int i = 0; i < operands.size()-1; i++) {
      sb.append(operands.get(i).toStringShort());
    }
    sb.append(") (").append(operands.get(operands.size()-1)).append(")");
    return sb.toString();
  }
  
  @Override
  public boolean equals(Object t) {
    if(!(t instanceof RefType))   return false;
    LambdaType ft = (LambdaType) t;
    return EqualsUtil.areEqual(operands, ft.operands);
  }
	
	ValueTypeKind getKind() {
		return ValueTypeKind.LAMBDA;
	}
	
	Collection<ECR> getOperands() {
		return operands;
	}

}
