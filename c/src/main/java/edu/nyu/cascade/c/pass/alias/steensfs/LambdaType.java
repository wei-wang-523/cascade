package edu.nyu.cascade.c.pass.alias.steensfs;

import java.util.List;

import com.google.common.collect.Lists;

import edu.nyu.cascade.util.EqualsUtil;

class LambdaType extends ValueType {
	private final List<ECR> params;
	private final ECR ret;
	private Size size;
	private Parent parent;
	
	LambdaType(ECR ret, List<ECR> args, Size size, Parent parent) {
		this.params = Lists.newArrayList(args);
		this.ret = ret;
		this.size = size;
		this.parent = parent;
	}

	@Override
  public String toString() {
    StringBuilder sb = new StringBuilder()
    .append("LAMBDA (").append(params).append("->").append(ret).append(")");
    return sb.toString();
  }
  
  @Override
  public boolean equals(Object t) {
    if(!(t instanceof LambdaType))   return false;
    LambdaType ft = (LambdaType) t;
    return EqualsUtil.areEqual(params, ft.params) && ret.equals(ft.ret);
  }
	
	ValueTypeKind getKind() {
		return ValueTypeKind.LAMBDA;
	}
	
	List<ECR> getParams() {
		return params;
	}
	
	ECR getRet() {
		return ret;
	}

	/**
	 * Used for add parameter ECR for function type with empty param-types
	 * 
	 * The use of function declarators with empty parentheses (not prototype
	 * -format parameter type declarators) is an obsolescent feature.
	 * 
	 * @param paramECR
	 */
	void addParamECR(ECR paramECR) {
	  params.add(paramECR);
  }

	@Override
	Size getSize() {
		return size;
	}

	@Override
	void setSize(Size size) {
		this.size = size;
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
