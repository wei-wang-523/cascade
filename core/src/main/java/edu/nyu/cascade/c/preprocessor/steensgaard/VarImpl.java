package edu.nyu.cascade.c.preprocessor.steensgaard;

import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

import xtc.type.PointerT;
import xtc.type.Type;
import edu.nyu.cascade.c.CType;
import edu.nyu.cascade.c.preprocessor.IRVar;
import edu.nyu.cascade.ir.IRVarInfo;
import edu.nyu.cascade.prover.Expression;
import edu.nyu.cascade.util.Pair;

class VarImpl implements IRVar {
  private final ECR ecr;
  private final String name;
  private final Type type;
  private final String scopeName;
  private final Expression srcExpr;
  private final Map<String, Object> properties;
  
  private boolean heapTag = false;
  
  private VarImpl(String name, Type type, String scopeName, Expression srcExpr, ECR ecr) {
    this.name = name;
    this.type = type;
    this.scopeName = scopeName;
    this.srcExpr = srcExpr;
    this.ecr = ecr;
    this.properties = Maps.newHashMap();
  }
  
  static VarImpl createCtrlSymbol(IRVarInfo info) {
  	Preconditions.checkArgument(info.hasRValBinding());
  	
  	Type xtcType = info.getXtcType().resolve();
    assert(!(xtcType.isArray() || xtcType.isUnion() || xtcType.isStruct()));
  	
  	String scopeName = info.getScopeName();
    
    ECR loc = ECR.createBottom();
    ECR func = ECR.createBottom();
    ValueType type = ValueType.ref(loc, func, xtcType, scopeName);
  	ECR resECR = ECR.create(type);
  	
  	loc.getType().setAddress(resECR);
  	func.getType().setAddress(resECR);
    
  	return new VarImpl(info.getName(), xtcType, scopeName, info.getLValBinding(), resECR);
  }
  
  /**
   * Create an IRVar for a symbol with scalar type <code>type</code>
   * @param name
   * @param type
   * @param scopeName
   * @param srcExpr
   * @return
   */
  static VarImpl createForScalarSymbol(
  		String name, Type type, String scopeName, Expression srcExpr) {
    ECR loc = ECR.createBottom();
    ECR func = ECR.createBottom();
    
    ValueType refType = ValueType.ref(loc, func, type, scopeName);
  	ECR varECR = ECR.create(refType);
  	
  	loc.getType().setAddress(varECR);
  	func.getType().setAddress(varECR);
    
    // For scalar type variable, set the address
  	ECR addrFunc = ECR.createBottom();
  	ECR addrECR = ECR.create(ValueType.ref( varECR, addrFunc, 
  			new PointerT(type), scopeName));
  	
  	varECR.getType().setAddress(addrECR);
  	addrFunc.getType().setAddress(addrECR);
    
  	return new VarImpl(name, type, scopeName, srcExpr, varECR);
  }
  
  /**
   * Create an IRVar for a symbol with array type
   * @param name
   * @param type
   * @param scopeName
   * @param srcExpr
   * @return
   */
  static Pair<VarImpl, VarImpl> createForArraySymbol(
  		String name, Type type, String scopeName, Expression srcExpr) {
  	Preconditions.checkArgument(type.resolve().isArray());
    
		ECR regLoc = ECR.createBottom();
		ECR regFunc = ECR.createBottom();
		
		ValueType regType = ValueType.ref(
				regLoc, regFunc, CType.getCellType(type.resolve()), scopeName);
		ECR regECR = ECR.create(regType);
		
		regLoc.getType().setAddress(regECR);
		regFunc.getType().setAddress(regECR);
		
		String regName = "array(" + name + ")";
		
		VarImpl regVar = new VarImpl(regName, type, scopeName, srcExpr, regECR);
		
		ECR loc = regECR;
    ECR func = ECR.createBottom();
    
    ValueType varType = ValueType.ref(loc, func, type, scopeName);
  	ECR varECR = ECR.create(varType);
  	
  	loc.getType().setAddress(varECR);
  	func.getType().setAddress(varECR);
  	
  	varType.setAddress(varECR);
    
  	VarImpl resVar = new VarImpl(name, new PointerT(type), scopeName, srcExpr, varECR);
  	
    return Pair.of(resVar, regVar);
  }
  
  /**
   * Create an IRVar for a symbol with struct or union type
   * @param name
   * @param type
   * @param scopeName
   * @param srcExpr
   * @return
   */
  static Pair<VarImpl, VarImpl> createForStructOrUnionSymbol(
  		String name, Type type, String scopeName, Expression srcExpr) {
  	Preconditions.checkArgument(type.resolve().isStruct() || type.resolve().isUnion());
    
		ECR regLoc = ECR.createBottom();
		ECR regFunc = ECR.createBottom();
		
		ValueType regType = ValueType.ref(
				regLoc, regFunc, CType.getCellType(type), scopeName);
		ECR regECR = ECR.create(regType);
		
		regLoc.getType().setAddress(regECR);
		regFunc.getType().setAddress(regECR);
		
		String regName = "struct(" + name + ")";
		VarImpl regVar = new VarImpl(regName, type, scopeName, srcExpr, regECR);
		
		ECR loc = regECR;
    ECR func = ECR.createBottom();
    
    ValueType refType = ValueType.ref(loc, func, type, scopeName);
  	ECR varECR = ECR.create(refType);
  	
  	loc.getType().setAddress(varECR);
  	func.getType().setAddress(varECR);
  	
  	varECR.getType().setAddress(varECR);
    
  	VarImpl resVar = new VarImpl(name, type, scopeName, srcExpr, varECR);
  	
    return Pair.of(resVar, regVar);
  }
  
  static VarImpl createRegionVar(String name, Type type, String scopeName, Expression srcExpr) {    
  	ECR loc = ECR.createBottom();
    ECR func = ECR.createBottom();
    
    ValueType refType = ValueType.ref(loc, func, CType.getCellType(type.resolve()), scopeName);
  	ECR resECR = ECR.create(refType);
  	
  	loc.getType().setAddress(resECR);
  	func.getType().setAddress(resECR);
  	
  	VarImpl resVar = new VarImpl(name, type, scopeName, srcExpr, resECR);
  	resVar.heapTag = true;
    return resVar;
  }
  
  ECR getECR() {
    return (ECR) ecr.findRoot();
  }
  
  @Override
  public String toString() {
  	StringBuilder sb = new StringBuilder();
  	sb.append(srcExpr).append(": ").append(name).append('@').append(scopeName);
  	return sb.toString();
  }

	@Override
  public String toStringShort() {
	  return srcExpr.toString();
  }

	@Override
  public String getName() {
	  return name;
  }

	@Override
  public Type getType() {
	  return type;
  }

	@Override
  public String getScopeName() {
	  return scopeName;
  }

	@Override
  public Expression getExpr() {
	  return srcExpr;
  }
	
	@Override
	public boolean hasHeapTag() {
		return heapTag;
	}

	@Override
  public void setProperty(String id, Object o) {
	  properties.put(id, o);
  }

	@Override
  public Object getProperty(String id) {
	  return properties.get(id);
  }
}