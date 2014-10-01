package edu.nyu.cascade.c.preprocessor.steensgaard;

class RefType extends ValueType {
	
	private final ECR loc, func;
	private final xtc.type.Type xtcType;
	private final String scopeName;
	
	RefType(ECR loc, ECR func, xtc.type.Type xtcType, String scopeName) {
		this.loc = loc;
		this.func = func;
		this.xtcType = xtcType;
		this.scopeName = scopeName;
	}
	
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder()
    		.append("REF ( ")
        .append(((ECR) loc.findRoot()).getId())
        .append(" * ")
        .append(((ECR) func.findRoot()).getId())
        .append(" )");
    return sb.toString();
  }
  
  @Override
  public boolean equals(Object t) {
    if(!(t instanceof RefType))   return false;
    RefType vt = (RefType) t;
    if(!loc.equals(vt.loc)) return false;
    if(!func.equals(vt.func)) return false;
    return true;
  }
	
	ValueTypeKind getKind() {
		return ValueTypeKind.REF;
	}
	
	ECR getLocation() {
		return loc;
	}
	
	ECR getFunction() {
		return func;
	}
	
	xtc.type.Type getXtcType() {
		return xtcType;
	}
	
	String getScopeName() {
		return scopeName;
	}
}
