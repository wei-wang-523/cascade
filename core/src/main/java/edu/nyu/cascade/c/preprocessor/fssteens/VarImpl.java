package edu.nyu.cascade.c.preprocessor.fssteens;

import java.util.Map;

import com.google.common.base.Preconditions;
import com.google.common.collect.Maps;

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
  
  static VarImpl createForCtrlSymbol(IRVarInfo info) {
  	Preconditions.checkArgument(info.hasRValBinding());
  	
  	Type xtcType = info.getXtcType().resolve();
  	assert(!(xtcType.isArray() || xtcType.isUnion() || xtcType.isStruct()));
  	
    String scopeName = info.getScopeName();
    
    Parent parent = Parent.getEmpty();
    BlankType type = ValueType.blank(Size.createForType(xtcType), parent, scopeName);
    
  	ECR resECR = ECR.create(type);
  	
    return new VarImpl(info.getName(), xtcType, scopeName, info.getLValBinding(), resECR);
  }
  
  /**
   * Create an IRVar for a symbol with struct or union type
   * @param name
   * @param xtcType
   * @param scopeName
   * @param srcExpr
   * @return
   */
  static Pair<VarImpl, VarImpl> createForStructOrUnionSymbol(
  		String name, Type xtcType, String scopeName, Expression srcExpr) {
  	Preconditions.checkArgument(xtcType.resolve().isStruct() || xtcType.resolve().isUnion());
		
    BlankType regionType = ValueType.blank(
    		Size.createForType(xtcType), Parent.getEmpty(), scopeName);
    
  	ECR regECR = ECR.create(regionType);
  	VarImpl regVar = new VarImpl(name, xtcType, scopeName, srcExpr, regECR);
    
		SimpleType varType = ValueType.simple(
				Pair.of(regECR, Offset.createZero()), 
				Function.getBottom(), 
				Size.createForType(xtcType), 
				Parent.getEmpty(), 
				xtcType, 
				scopeName);
		
		ECR varECR = ECR.create(varType);
		regionType.setAddress(varECR);
		varType.setAddress(varECR);
  	
  	VarImpl var = new VarImpl(name, xtcType, scopeName, srcExpr, varECR);
  	
    return Pair.of(var, regVar);
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
  		String name, Type xtcType, String scopeName, Expression srcExpr) {
  	Preconditions.checkArgument(xtcType.resolve().isArray());
  	
    BlankType blankType = ValueType.blank(
    		Size.createForType(xtcType), Parent.getEmpty(), scopeName);
    
  	ECR regECR = ECR.create(blankType);
  	VarImpl regVar = new VarImpl(name, xtcType, scopeName, srcExpr, regECR);
    
    Pair<ECR, Offset> loc = Pair.of(regECR, Offset.createZero());
    SimpleType varType = ValueType.simple(loc, Function.getBottom(), 
    		Size.createForType(xtcType), 
    		Parent.getEmpty(),
    		xtcType,
    		scopeName);
    
  	ECR varECR = ECR.create(varType);
  	blankType.setAddress(varECR);
  	
  	VarImpl var = new VarImpl(name, xtcType, scopeName, srcExpr, varECR);
  	
    return Pair.of(var, regVar);
  }
  
  static VarImpl createForScalarSymbol(
  		String name, Type xtcType, String scopeName, Expression srcExpr) {
  	Parent parent = Parent.getEmpty();
    BlankType blankType = ValueType.blank(
    		Size.createForType(xtcType), parent, scopeName);
    
  	ECR varECR = ECR.create(blankType);
    
  	return new VarImpl(name, xtcType, scopeName, srcExpr, varECR);
  }
  
  static VarImpl createRegionVar(String name, Type xtcType,
	    String scopeName, Expression region) {    
    Parent parent = Parent.getEmpty();
    BlankType type = ValueType.blank(
    		Size.createForType(xtcType), parent, scopeName);
    
  	ECR regECR = ECR.create(type);
  	
    VarImpl regVar = new VarImpl(name, xtcType, scopeName, region, regECR);
    regVar.heapTag = true;
    return regVar;
	}

  ECR getECR() {
    return (ECR) ecr.findRoot();
  }
  
	@Override
  public String toString() {
		StringBuilder sb = new StringBuilder();
		
		sb.append(name).append('@').append(scopeName)
			.append(" (").append(CType.parseTypeName(type))
			.append(") : ").append(srcExpr);
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
  public void setProperty(String id, Object o) {
	  properties.put(id, o);
  }

	@Override
  public Object getProperty(String id) {
	  return properties.get(id);
  }

	@Override
  public Expression getExpr() {
	  return srcExpr;
  }

	@Override
  public boolean hasHeapTag() {
	  return heapTag;
  }
}
